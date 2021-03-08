package org.group_mmm;

import lombok.extern.slf4j.Slf4j;

import java.util.List;
import java.util.function.Function;

/**
 * <p>STLVisitorImpl class.</p>
 *
 * @author Masaki Waga {@literal <masakiwaga@gmail.com>}
 */
@Slf4j
public class SignalMapperVisitorImpl extends org.group_mmm.SignalMapperBaseVisitor<Function<List<Double>, Double>> {
    /**
     * {@inheritDoc}
     */
    @Override
    public Function<List<Double>, Double> visitExpr(org.group_mmm.SignalMapperParser.ExprContext ctx) {
        if (ctx.atomic() != null) {
            // atomic
            log.trace("atomic");
            return visitAtomic(ctx.atomic());
        } else if (ctx.TIMES() != null) {
            // times
            log.trace("times");
            assert ctx.expr().size() == 2;
            return (concreteSignal) -> visitExpr(ctx.left).apply(concreteSignal) * visitExpr(ctx.expr(1)).apply(concreteSignal);
        } else if (ctx.DIV() != null) {
            // div
            log.trace("div");
            assert ctx.expr().size() == 2;
            return (concreteSignal) -> visitExpr(ctx.left).apply(concreteSignal) / visitExpr(ctx.expr(1)).apply(concreteSignal);
        } else if (ctx.PLUS() != null) {
            // plus
            log.trace("plus");
            assert ctx.expr().size() == 2;
            return (concreteSignal) -> visitExpr(ctx.left).apply(concreteSignal) + visitExpr(ctx.expr(1)).apply(concreteSignal);
        } else if (ctx.MINUS() != null) {
            // minus
            log.trace("minus");
            assert ctx.expr().size() == 2;
            return (concreteSignal) -> visitExpr(ctx.left).apply(concreteSignal) - visitExpr(ctx.expr(1)).apply(concreteSignal);
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
    public Function<List<Double>, Double> visitAtomic(org.group_mmm.SignalMapperParser.AtomicContext ctx) {
        if (ctx.signalID != null) {
            int sigIndex = Integer.parseInt(ctx.signalID.getText());
            return (concreteSignal) -> concreteSignal.get(sigIndex);
        } else {
            double value = Double.parseDouble(ctx.value().getText());
            return (concreteSignal) -> value;
        }
    }
}
