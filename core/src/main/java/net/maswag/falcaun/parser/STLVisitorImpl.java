package net.maswag.falcaun;

import lombok.AllArgsConstructor;
import lombok.NoArgsConstructor;
import lombok.extern.slf4j.Slf4j;
import net.maswag.falcaun.TemporalImply.STLImply;
import net.maswag.falcaun.TemporalRelease.STLRelease;

import java.util.List;
import java.util.Map;

import static net.maswag.falcaun.STLAbstractAtomic.Operation.*;

/**
 * <p>STLVisitorImpl class.</p>
 *
 * @author Masaki Waga {@literal <masakiwaga@gmail.com>}
 */
@Slf4j
@NoArgsConstructor
@AllArgsConstructor
public class STLVisitorImpl extends net.maswag.falcaun.STLBaseVisitor<TemporalLogic.STLCost> {
    private List<Map<Character, Double>> inputMapper;
    private List<Map<Character, Double>> outputMapper;
    private List<Character> largest;

    private TemporalLogic.STLCost handleInterval(TemporalOp<List<Double>> subFml, net.maswag.falcaun.STLParser.IntervalContext ctx) {
        assert (ctx != null);
        log.trace("Bounded Globally or Eventually");
        int from = Integer.parseInt(ctx.left.getText());
        int to = Integer.parseInt(ctx.right.getText());
        return new TemporalSub.STLSub(subFml, from, to);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public TemporalLogic.STLCost visitExpr(net.maswag.falcaun.STLParser.ExprContext ctx) {
        if (ctx.atomic() != null) {
            // atomic
            log.trace("atomic");
            return visitAtomic(ctx.atomic());
        } else if (ctx.binaryOperator() != null) {
            // Binary operators without interval
            TemporalLogic.STLCost left = visitExpr(ctx.left);
            TemporalLogic.STLCost right = visitExpr(ctx.right);
            if (ctx.binaryOperator().OR() != null) {
                log.trace("or");
                return new TemporalOr.STLOr(left, right);
            } else if (ctx.binaryOperator().AND() != null) {
                log.trace("and");
                return new TemporalAnd.STLAnd(left, right);
            } else if (ctx.binaryOperator().IMPLY() != null) {
                log.trace("imply");
                return new STLImply(left, right);
            } else if (ctx.binaryOperator().binaryTemporalOperator().UNTIL() != null) {
                log.trace("until");
                return new TemporalUntil.STLUntil(left, right);
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
            TemporalLogic.STLCost expr = visitExpr(ctx.expr(0));
            if (ctx.unaryOperator().NEXT() != null) {
                log.trace("next");
                return new TemporalNext.STLNext(expr, true);
            } else if (ctx.unaryOperator().unaryTemporalOperator() != null && ctx.unaryOperator().unaryTemporalOperator().GLOBALLY() != null) {
                log.trace("Globally");
                return new TemporalGlobally.STLGlobally(expr);
            } else if (ctx.unaryOperator().unaryTemporalOperator() != null && ctx.unaryOperator().unaryTemporalOperator().EVENTUALLY() != null) {
                log.trace("Eventually");
                return new TemporalEventually.STLEventually(expr);
            } else if (ctx.unaryOperator().NOT() != null) {
                log.trace("not");
                return new TemporalNot.STLNot(expr);
            } else {
                log.error("Unimplemented formula!!");
                throw new UnsupportedOperationException("Unimplemented formula");
            }
        } else if (ctx.unaryTemporalOperator() != null) {
            // Unary operators with interval
            assert ctx.expr().size() == 1;
            TemporalLogic.STLCost expr = visitExpr(ctx.expr(0));
            if (ctx.unaryTemporalOperator().GLOBALLY() != null) {
                log.trace("Globally");
                TemporalGlobally.STLGlobally global = new TemporalGlobally.STLGlobally(expr);

                return handleInterval(global, ctx.interval());
            } else if (ctx.unaryTemporalOperator().EVENTUALLY() != null) {
                log.trace("Eventually");
                TemporalEventually.STLEventually eventually = new TemporalEventually.STLEventually(expr);

                return handleInterval(eventually, ctx.interval());
            }
        } else if (ctx.binaryTemporalOperator() != null) {
            // Binary operators with interval
            TemporalLogic.STLCost left = visitExpr(ctx.left);
            TemporalLogic.STLCost right = visitExpr(ctx.right);
            if (ctx.binaryTemporalOperator().UNTIL() != null) {
                log.trace("Until");
                TemporalUntil.STLUntil until = new TemporalUntil.STLUntil(left, right);

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
    public TemporalLogic.STLCost visitAtomic(net.maswag.falcaun.STLParser.AtomicContext ctx) {
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
