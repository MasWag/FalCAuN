package org.group_mmm;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.util.AbstractMap;
import java.util.List;
import java.util.Map;

import static org.group_mmm.STLAtomic.Operation.*;

public class STLVisitorImpl extends org.group_mmm.STLBaseVisitor {
    private static final Logger LOGGER = LoggerFactory.getLogger(STLVisitorImpl.class);
    private List<Map<Character, Double>> outputMapper;
    private List<Character> largest;


    STLVisitorImpl() {
        this.outputMapper = null;
        this.largest = null;
    }

    STLVisitorImpl(List<Map<Character, Double>> outputMapper, List<Character> largest) {
        this.outputMapper = outputMapper;
        this.largest = largest;
    }

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
            LOGGER.trace("Bounded Globally");
            @SuppressWarnings("unchecked")
            AbstractMap.SimpleEntry<Integer, Integer> interval = (AbstractMap.SimpleEntry<Integer, Integer>) visitInterval(ctx);
            int from = interval.getKey();
            int to = interval.getValue();
            return new STLSub(subFml, from, to);
        }
    }

    @Override
    public Object visitExpr(org.group_mmm.STLParser.ExprContext ctx) {
        if (ctx.atomic() != null) {
            // atomic
            LOGGER.trace("atomic");
            return visitAtomic(ctx.atomic());
        } else if (ctx.OR() != null) {
            // or
            LOGGER.trace("or");
            assert ctx.expr().size() == 2;
            return new STLOr((STLCost) visitExpr(ctx.expr(0)), (STLCost) visitExpr(ctx.expr(1)));
        } else if (ctx.IMPLY() != null) {
            // imply
            LOGGER.trace("imply");
            assert ctx.expr().size() == 2;
            return new STLImply((STLCost) visitExpr(ctx.left), (STLCost) visitExpr(ctx.right));
        } else if (ctx.NEXT() != null) {
            // Next
            LOGGER.trace("next");
            assert ctx.expr().size() == 1;
            return new STLNext((STLCost) visitExpr(ctx.expr(0)), true);
        } else if (ctx.GLOBALLY() != null) {
            // Globally
            LOGGER.trace("Globally");
            assert ctx.expr().size() == 1;
            STLGlobal global = new STLGlobal((STLCost) visitExpr(ctx.expr(0)));

            return handleInterval(global, ctx.interval());
        } else if (ctx.EVENTUALLY() != null) {
            // Eventually
            LOGGER.trace("Eventually");
            assert ctx.expr().size() == 1;
            STLEventually eventually = new STLEventually((STLCost) visitExpr(ctx.expr(0)));

            return handleInterval(eventually, ctx.interval());
        } else if (ctx.LPAREN() != null) {
            // Paren
            LOGGER.trace("paren");
            assert ctx.expr().size() == 1;
            return visitExpr(ctx.expr(0));
        }

        LOGGER.error("Unimplemented formula!!");
        return null;
    }

    @Override
    public Object visitAtomic(org.group_mmm.STLParser.AtomicContext ctx) {
        int sigIndex = Integer.parseInt(ctx.signalID.getText());

        STLAtomic.Operation op;
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
            default:
                throw new UnsupportedOperationException();
        }

        double comparator = Double.valueOf(ctx.value().getText());

        STLAtomic result = new STLAtomic(sigIndex, op, comparator);
        if (this.outputMapper != null && this.largest != null) {
            result.setOutputMapper(outputMapper);
            result.setLargest(largest);
        }

        return result;
    }
}
