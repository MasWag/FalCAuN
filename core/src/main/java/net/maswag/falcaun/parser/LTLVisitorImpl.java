package net.maswag.falcaun.parser;

import lombok.AllArgsConstructor;
import lombok.NoArgsConstructor;
import lombok.extern.slf4j.Slf4j;
import net.maswag.falcaun.parser.TemporalAnd.LTLAnd;
import net.maswag.falcaun.parser.TemporalEventually.LTLEventually;
import net.maswag.falcaun.parser.TemporalGlobally.LTLGlobally;
import net.maswag.falcaun.parser.TemporalImply.LTLImply;
import net.maswag.falcaun.parser.TemporalLogic.LTLFormula;
import net.maswag.falcaun.parser.TemporalNext.LTLNext;
import net.maswag.falcaun.parser.TemporalNot.LTLNot;
import net.maswag.falcaun.parser.TemporalOr.LTLOr;
import net.maswag.falcaun.parser.TemporalRelease.LTLRelease;
import net.maswag.falcaun.parser.TemporalSub.LTLSub;
import net.maswag.falcaun.parser.TemporalUntil.LTLUntil;
import net.maswag.falcaun.parser.LTLBaseVisitor;
import net.maswag.falcaun.parser.LTLParser;

import java.util.List;
import java.util.Map;
import java.util.Optional;


/**
 * <p>LTLVisitorImpl class.</p>
 *
 * @author Masaki Waga {@literal <masakiwaga@gmail.com>}
 */
@Slf4j
@NoArgsConstructor
@AllArgsConstructor
public class LTLVisitorImpl extends LTLBaseVisitor<TemporalLogic.LTLFormula> {
    private List<Map<Character, Double>> inputMapper;
    private List<Map<Character, Double>> outputMapper;
    private List<Character> largest;

    private TemporalLogic.LTLFormula handleInterval(TemporalOp<String> subFml, LTLParser.IntervalContext ctx) {
        log.trace("Bounded Globally or Eventually");
        int from = Integer.parseInt(ctx.left.getText());
        int to = Integer.parseInt(ctx.right.getText());
        return new TemporalSub.LTLSub(subFml, from, to);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public TemporalLogic.LTLFormula visitExpr(LTLParser.ExprContext ctx) {
        if (ctx.INPUT() != null) {
            // atomic
            log.trace("atomic input");
            return new LTLAtomic(Optional.of(ctx.ID().getText()), Optional.empty());
        } else if (ctx.OUTPUT() != null) {
            // atomic
            log.trace("atomic output");
            return new LTLAtomic(Optional.empty(), Optional.of(ctx.ID().getText()));
        } else if (ctx.binaryOperator() != null) {
            // Binary operators without interval
            TemporalLogic.LTLFormula left = visitExpr(ctx.left);
            TemporalLogic.LTLFormula right = visitExpr(ctx.right);
            if (ctx.binaryOperator().OR() != null) {
                log.trace("or");
                return new TemporalOr.LTLOr(left, right);
            } else if (ctx.binaryOperator().AND() != null) {
                log.trace("and");
                return new TemporalAnd.LTLAnd(left, right);
            } else if (ctx.binaryOperator().IMPLY() != null) {
                log.trace("imply");
                return new LTLImply(left, right);
            } else if (ctx.binaryOperator().binaryTemporalOperator().UNTIL() != null) {
                log.trace("until");
                return new TemporalUntil.LTLUntil(left, right);
            } else if (ctx.binaryOperator().binaryTemporalOperator().RELEASE() != null) {
                log.trace("release");
                return new LTLRelease(left, right);
            } else {
                log.error("Unimplemented formula!!");
                throw new UnsupportedOperationException("Unimplemented formula");
            }
        } else if (ctx.unaryOperator() != null) {
            // Unary operators without interval
            assert ctx.expr().size() == 1;
            TemporalLogic.LTLFormula expr = visitExpr(ctx.expr(0));
            if (ctx.unaryOperator().NEXT() != null) {
                log.trace("next");
                return new TemporalNext.LTLNext(expr, true);
            } else if (ctx.unaryOperator().unaryTemporalOperator() != null && ctx.unaryOperator().unaryTemporalOperator().GLOBALLY() != null) {
                log.trace("Globally");
                return new TemporalGlobally.LTLGlobally(expr);
            } else if (ctx.unaryOperator().unaryTemporalOperator() != null && ctx.unaryOperator().unaryTemporalOperator().EVENTUALLY() != null) {
                log.trace("Eventually");
                return new TemporalEventually.LTLEventually(expr);
            } else if (ctx.unaryOperator().NOT() != null) {
                log.trace("not");
                return new TemporalNot.LTLNot(expr);
            } else {
                log.error("Unimplemented formula!!");
                throw new UnsupportedOperationException("Unimplemented formula");
            }
        } else if (ctx.unaryTemporalOperator() != null) {
            // Unary operators with interval
            assert ctx.expr().size() == 1;
            TemporalLogic.LTLFormula expr = visitExpr(ctx.expr(0));
            if (ctx.unaryTemporalOperator().GLOBALLY() != null) {
                log.trace("Globally");
                TemporalGlobally.LTLGlobally global = new TemporalGlobally.LTLGlobally(expr);

                return handleInterval(global, ctx.interval());
            } else if (ctx.unaryTemporalOperator().EVENTUALLY() != null) {
                log.trace("Eventually");
                TemporalEventually.LTLEventually eventually = new TemporalEventually.LTLEventually(visitExpr(ctx.expr(0)));

                return handleInterval(eventually, ctx.interval());
            }
        } else if (ctx.binaryTemporalOperator() != null) {
            // Binary operators with interval
            TemporalLogic.LTLFormula left = visitExpr(ctx.left);
            TemporalLogic.LTLFormula right = visitExpr(ctx.right);
            if (ctx.binaryTemporalOperator().UNTIL() != null) {
                log.trace("Until");
                TemporalUntil.LTLUntil until = new TemporalUntil.LTLUntil(left, right);

                if (ctx.interval() != null) {
                    log.error("Bounded until is not implemented yet");
                    return null;
                } else {
                    return until;
                }
            } else if (ctx.binaryTemporalOperator().RELEASE() != null) {
                log.trace("Release");
                LTLRelease release = new LTLRelease(left, right);

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
}
