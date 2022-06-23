package org.group_mmm;

import lombok.extern.slf4j.Slf4j;

import java.util.List;
import java.util.Objects;
import java.util.function.Function;

import static java.lang.Math.abs;

/**
 * <p>STLVisitorImpl class.</p>
 *
 * @author Masaki Waga {@literal <masakiwaga@gmail.com>}
 */
@Slf4j
public class SignalMapperVisitorImpl extends org.group_mmm.SignalMapperBaseVisitor<Function<SimulinkSUL.IOSignalPiece, Double>> {
    /**
     * {@inheritDoc}
     */
    @Override
    public Function<SimulinkSUL.IOSignalPiece, Double> visitExpr(org.group_mmm.SignalMapperParser.ExprContext ctx) {
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
        }else if (ctx.ABS() != null) {
            // Paren
            log.trace("abs");
            assert ctx.expr().size() == 1;
            return (concreteSignal) -> abs(visitExpr(ctx.expr(0)).apply(concreteSignal));
        }

        log.error("Unimplemented formula!!");
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Function<SimulinkSUL.IOSignalPiece, Double> visitAtomic(org.group_mmm.SignalMapperParser.AtomicContext ctx) {
        if (ctx.signalID != null) {
            int sigIndex = Integer.parseInt(ctx.signalID.getText());
            if (Objects.nonNull(ctx.INPUT())) {
                return (concreteSignal) -> concreteSignal.getInputSignal().get(sigIndex);
            } else {
                return (concreteSignal) -> concreteSignal.getOutputSignal().get(sigIndex);
            }
        } else {
            double value = Double.parseDouble(ctx.value().getText());
            return (concreteSignal) -> value;
        }
    }
}
