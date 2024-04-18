package net.maswag;

import lombok.extern.slf4j.Slf4j;

import java.util.List;
import java.util.Objects;
import java.util.function.Function;

import static java.lang.Math.abs;

/**
 * <p>ExtendedSignalMapperVisitorImpl class.</p>
 *
 * @author Masaki Waga {@literal <masakiwaga@gmail.com>}
 */
@Slf4j
public class ExtendedSignalMapperVisitorImpl extends net.maswag.ExtendedSignalMapperBaseVisitor<Function<ExtendedIOSignalPiece<List<Double>>, Double>> {
    /**
     * {@inheritDoc}
     */
    @Override
    public Function<ExtendedIOSignalPiece<List<Double>>, Double> visitExpr(net.maswag.ExtendedSignalMapperParser.ExprContext ctx) {
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
    public Function<ExtendedIOSignalPiece<List<Double>>, Double> visitAtomic(net.maswag.ExtendedSignalMapperParser.AtomicContext ctx) {
        if (ctx.signalID != null) {
            int sigIndex = Integer.parseInt(ctx.signalID.getText());
            if (Objects.nonNull(ctx.INPUT())) {
                return (concreteSignal) -> concreteSignal.getInputSignal().get(sigIndex);
            } else if (Objects.nonNull(ctx.OUTPUT())) {
                return (concreteSignal) -> concreteSignal.getOutputSignal().get(sigIndex);
            } else if (Objects.nonNull(ctx.PREVIOUS_MAX_OUTPUT())) {
                return (concreteSignal) -> concreteSignal.getPreviousOutputSignals().stream()
                        // Take the elementwise maximum of the previous output signals
                        .reduce((a, b) -> {
                            assert a.size() == b.size();
                            for (int i = 0; i < a.size(); i++) {
                                a.set(i, Math.max(a.get(i), b.get(i)));
                            }
                            return a;
                        }).get().get(sigIndex);
            } else { // PREVIOUS_MIN_OUTPUT
                return (concreteSignal) -> concreteSignal.getPreviousOutputSignals().stream()
                        // Take the elementwise minimum of the previous output signals
                        .reduce((a, b) -> {
                            assert a.size() == b.size();
                            for (int i = 0; i < a.size(); i++) {
                                a.set(i, Math.min(a.get(i), b.get(i)));
                            }
                            return a;
                        }).get().get(sigIndex);
            }
        } else {
            double value = Double.parseDouble(ctx.value().getText());
            return (concreteSignal) -> value;
        }
    }
}
