package net.maswag;

import lombok.AllArgsConstructor;
import lombok.NoArgsConstructor;
import lombok.extern.slf4j.Slf4j;

import java.util.List;
import java.util.Map;

import static net.maswag.STLAbstractAtomic.Operation.*;

/**
 * <p>STLVisitorImpl class.</p>
 *
 * @author Masaki Waga {@literal <masakiwaga@gmail.com>}
 */
@Slf4j
@NoArgsConstructor
@AllArgsConstructor
public class STLVisitorImpl extends net.maswag.STLBaseVisitor<STLCost> {
    private List<Map<Character, Double>> inputMapper;
    private List<Map<Character, Double>> outputMapper;
    private List<Character> largest;

    private STLCost handleInterval(STLTemporalOp subFml, net.maswag.STLParser.IntervalContext ctx) {

        if (ctx == null) {
            return subFml;
        } else {
            log.trace("Bounded Globally or Eventually");
            int from = Integer.parseInt(ctx.left.getText());
            int to = Integer.parseInt(ctx.right.getText());
            return new STLSub(subFml, from, to);
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public STLCost visitExpr(net.maswag.STLParser.ExprContext ctx) {
        if (ctx.atomic() != null) {
            // atomic
            log.trace("atomic");
            return visitAtomic(ctx.atomic());
        } else if (ctx.binaryOperator() != null) {
            // Binary operators without interval
            STLCost left = visitExpr(ctx.left);
            STLCost right = visitExpr(ctx.right);
            if (ctx.binaryOperator().OR() != null) {
                log.trace("or");
                return new STLOr(left, right);
            } else if (ctx.binaryOperator().AND() != null) {
                log.trace("and");
                return new STLAnd(left, right);
            } else if (ctx.binaryOperator().IMPLY() != null) {
                log.trace("imply");
                return new STLImply(left, right);
            } else if (ctx.binaryOperator().binaryTemporalOperator().UNTIL() != null) {
                log.trace("until");
                return new STLUntil(left, right);
            } else if (ctx.binaryOperator().binaryTemporalOperator().RELEASE() != null) {
                log.trace("release");
                return new STLRelease(left, right);
            } else {
                log.error("Unimplemented formula!!");
                throw new UnsupportedOperationException("Unimplemented formula");
            }
        } else if (ctx.unaryOperator() != null) {
            // Unary operators without interval
            assert ctx.expr().size() == 1;
            STLCost expr = visitExpr(ctx.expr(0));
            if (ctx.unaryOperator().NEXT() != null) {
                log.trace("next");
                return new STLNext(expr, true);
            } else if (ctx.unaryOperator().unaryTemporalOperator().GLOBALLY() != null) {
                log.trace("Globally");
                return new STLGlobal(expr);
            } else if (ctx.unaryOperator().unaryTemporalOperator().EVENTUALLY() != null) {
                log.trace("Eventually");
                return new STLEventually(expr);
            } else {
                log.error("Unimplemented formula!!");
                throw new UnsupportedOperationException("Unimplemented formula");
            }
        } else if (ctx.unaryTemporalOperator() != null) {
            // Unary operators with interval
            assert ctx.expr().size() == 1;
            STLCost expr = visitExpr(ctx.expr(0));
            if (ctx.unaryTemporalOperator().GLOBALLY() != null) {
                log.trace("Globally");
                STLGlobal global = new STLGlobal(expr);

                return handleInterval(global, ctx.interval());
            } else if (ctx.unaryTemporalOperator().EVENTUALLY() != null) {
                log.trace("Eventually");
                STLEventually eventually = new STLEventually(visitExpr(ctx.expr(0)));

                return handleInterval(eventually, ctx.interval());
            }
        } else if (ctx.binaryTemporalOperator() != null) {
            // Binary operators with interval
            STLCost left = visitExpr(ctx.left);
            STLCost right = visitExpr(ctx.right);
            if (ctx.binaryTemporalOperator().UNTIL() != null) {
                log.trace("Until");
                STLUntil until = new STLUntil(left, right);

                if (ctx.interval() != null) {
                    log.error("Bounded until is not implemented yet");
                    return null;
                } else {
                    return until;
                }
            } else if (ctx.binaryTemporalOperator().RELEASE() != null) {
                log.trace("Release");
                STLRelease release = new STLRelease(left, right);

                if (ctx.interval() != null) {
                    log.error("Bounded release is not implemented yet");
                    return null;
                } else {
                    return release;
                }
            } else {
                log.error("Unimplemented formula!!");
                throw new UnsupportedOperationException("Unimplemented formula");
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
    public STLCost visitAtomic(net.maswag.STLParser.AtomicContext ctx) {
        int sigIndex = Integer.parseInt(ctx.signalID.getText());

        STLAbstractAtomic.Operation op;
        switch (ctx.comparisonOperator().getText()) {
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
