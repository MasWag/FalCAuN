package org.group_mmm;

import lombok.AllArgsConstructor;
import lombok.NoArgsConstructor;
import lombok.extern.slf4j.Slf4j;

import java.util.AbstractMap;
import java.util.List;
import java.util.Map;

import static org.group_mmm.STLAbstractAtomic.Operation.*;

/**
 * <p>STLVisitorImpl class.</p>
 *
 * @author Masaki Waga {@literal <masakiwaga@gmail.com>}
 */
@Slf4j
@NoArgsConstructor
@AllArgsConstructor
public class STLVisitorImpl extends org.group_mmm.STLBaseVisitor {
    private List<Map<Character, Double>> inputMapper;
    private List<Map<Character, Double>> outputMapper;
    private List<Character> largest;

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visitInterval(org.group_mmm.STLParser.IntervalContext ctx) {
        int from = Integer.parseInt(ctx.left.getText());
        int to = Integer.parseInt(ctx.right.getText());

        return new AbstractMap.SimpleEntry<>(from, to);
    }

    private STLCost handleInterval(STLTemporalOp subFml, org.group_mmm.STLParser.IntervalContext ctx) {

        if (ctx == null) {
            return subFml;
        } else {
            log.trace("Bounded Globally");
            @SuppressWarnings("unchecked")
            AbstractMap.SimpleEntry<Integer, Integer> interval = (AbstractMap.SimpleEntry<Integer, Integer>) visitInterval(ctx);
            int from = interval.getKey();
            int to = interval.getValue();
            return new STLSub(subFml, from, to);
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visitExpr(org.group_mmm.STLParser.ExprContext ctx) {
        if (ctx.atomic() != null) {
            // atomic
            log.trace("atomic");
            return visitAtomic(ctx.atomic());
        } else if (ctx.OR() != null) {
            // or
            log.trace("or");
            assert ctx.expr().size() == 2;
            return new STLOr((STLCost) visitExpr(ctx.expr(0)), (STLCost) visitExpr(ctx.expr(1)));
        } else if (ctx.AND() != null) {
            // and
            log.trace("and");
            assert ctx.expr().size() == 2;
            return new STLAnd((STLCost) visitExpr(ctx.expr(0)), (STLCost) visitExpr(ctx.expr(1)));
        } else if (ctx.IMPLY() != null) {
            // imply
            log.trace("imply");
            assert ctx.expr().size() == 2;
            return new STLImply((STLCost) visitExpr(ctx.left), (STLCost) visitExpr(ctx.right));
        } else if (ctx.NEXT() != null) {
            // Next
            log.trace("next");
            assert ctx.expr().size() == 1;
            return new STLNext((STLCost) visitExpr(ctx.expr(0)), true);
        } else if (ctx.GLOBALLY() != null) {
            // Globally
            log.trace("Globally");
            assert ctx.expr().size() == 1;
            STLGlobal global = new STLGlobal((STLCost) visitExpr(ctx.expr(0)));

            return handleInterval(global, ctx.interval());
        } else if (ctx.EVENTUALLY() != null) {
            // Eventually
            log.trace("Eventually");
            assert ctx.expr().size() == 1;
            STLEventually eventually = new STLEventually((STLCost) visitExpr(ctx.expr(0)));

            return handleInterval(eventually, ctx.interval());
        } else if (ctx.UNTIL() != null) {
            // Until
            log.trace("Until");
            assert ctx.expr().size() == 2;
            STLUntil until = new STLUntil((STLCost) visitExpr(ctx.expr(0)), (STLCost) visitExpr(ctx.expr(1)));

            if (ctx.interval() != null) {
                log.error("Bounded until is not implemented yet");
                return null;
            } else {
                return until;
            }
        } else if (ctx.LPAREN() != null) {
            // Paren
            log.trace("paren");
            assert ctx.expr().size() == 1;
            return visitExpr(ctx.expr(0));
        }

        log.error("Unimplemented formula!!");
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object visitAtomic(org.group_mmm.STLParser.AtomicContext ctx) {
        int sigIndex = Integer.parseInt(ctx.signalID.getText());

        STLAbstractAtomic.Operation op;
        switch (ctx.operator.getText()) {
            case "==":
                op = eq;
                break;
            case "<":
                op = lt;
                break;
            case ">":
                op = gt;
                break;
            case "!=":
                op = ne;
                break;
            default:
                throw new UnsupportedOperationException();
        }

        double comparator = Double.parseDouble(ctx.value().getText());

        STLAbstractAtomic result;
        if (ctx.OUTPUT() != null) {
            STLOutputAtomic outputResult = new STLOutputAtomic(sigIndex, op, comparator);
            if (this.outputMapper != null && this.largest != null) {
                outputResult.setOutputMapper(outputMapper);
                outputResult.setLargest(largest);
            }
            result = outputResult;
        } else if (ctx.INPUT() != null) {
            STLInputAtomic inputResult = new STLInputAtomic(sigIndex, op, comparator);
            if (this.inputMapper != null) {
                inputResult.setInputMapper(inputMapper);
            }
            result = inputResult;
        } else {
            throw new UnsupportedOperationException();
        }
        return result;
    }
}
