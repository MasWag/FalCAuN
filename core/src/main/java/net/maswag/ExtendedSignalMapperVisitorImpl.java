package net.maswag;

import com.google.common.collect.Streams;
import lombok.extern.slf4j.Slf4j;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Objects;
import java.util.function.Function;
import java.util.stream.Collectors;

import static java.lang.Math.abs;
import net.maswag.ExtendedSignalMapperParser.*;

/**
 * <p>ExtendedSignalMapperVisitorImpl class.</p>
 *
 * @author Masaki Waga {@literal <masakiwaga@gmail.com>}
 */
@Slf4j
public class ExtendedSignalMapperVisitorImpl extends ExtendedSignalMapperBaseVisitor<Function<ExtendedIOSignalPiece<List<Double>>, List<Double>>> {
    /**
     * {@inheritDoc}
     */
    @Override
    public Function<ExtendedIOSignalPiece<List<Double>>, List<Double>> visitExpr(ExprContext ctx) {
        if (ctx.atomic() != null) {
            // atomic
            log.trace("atomic");
            return visitAtomic(ctx.atomic());
        } else if (ctx.TIMES() != null) {
            // times
            log.trace("times");
            assert ctx.expr().size() == 2;
            return (concreteSignal) ->
                    Streams.zip(visitExpr(ctx.left).apply(concreteSignal).stream(),
                            visitExpr(ctx.right).apply(concreteSignal).stream(),
                            (a, b) -> a * b).collect(Collectors.toList());
        } else if (ctx.DIV() != null) {
            // div
            log.trace("div");
            assert ctx.expr().size() == 2;
            return (concreteSignal) ->
                    Streams.zip(visitExpr(ctx.left).apply(concreteSignal).stream(),
                            visitExpr(ctx.right).apply(concreteSignal).stream(),
                            (a, b) -> a / b).collect(Collectors.toList());
        } else if (ctx.PLUS() != null) {
            // plus
            log.trace("plus");
            assert ctx.expr().size() == 2;
            return (concreteSignal) ->
                    Streams.zip(visitExpr(ctx.left).apply(concreteSignal).stream(),
                            visitExpr(ctx.expr(1)).apply(concreteSignal).stream(),
                            (a, b) -> a + b).collect(Collectors.toList());
        } else if (ctx.MINUS() != null) {
            // minus
            log.trace("minus");
            assert ctx.expr().size() == 2;
            return (concreteSignal) ->
                    Streams.zip(visitExpr(ctx.left).apply(concreteSignal).stream(),
                            visitExpr(ctx.right).apply(concreteSignal).stream(),
                            (a, b) -> a - b).collect(Collectors.toList());
        } else if (ctx.MOD() != null) {
            // mod
            log.trace("mod");
            assert ctx.expr().size() == 2;
            return (concreteSignal) ->
                    Streams.zip(visitExpr(ctx.left).apply(concreteSignal).stream(),
                            visitExpr(ctx.right).apply(concreteSignal).stream(),
                            (a, b) -> a % b).collect(Collectors.toList());
        } else if (ctx.ABS() != null) {
            // abs
            log.trace("abs");
            assert ctx.expr().size() == 1;
            return (concreteSignal) ->
                    visitExpr(ctx.expr(0)).apply(concreteSignal).stream().map(Math::abs).collect(Collectors.toList());
        } else if (ctx.MIN() != null) {
            // min
            log.trace("min");
            assert ctx.expr() != null;
            return (concreteSignal) -> Collections.singletonList(ctx.expr().stream().map(e -> visitExpr(e).apply(concreteSignal).get(0)).min(Double::compare).orElse(Double.POSITIVE_INFINITY));
        } else if (ctx.MAX() != null) {
            // max
            log.trace("max");
            assert ctx.expr() != null;
            return (concreteSignal) -> Collections.singletonList(ctx.expr().stream().map(e -> visitExpr(e).apply(concreteSignal).get(0)).max(Double::compare).orElse(Double.NEGATIVE_INFINITY));
        } else if (ctx.PREVIOUS_MAX() != null && ctx.extended_expr() != null) {
            log.trace("previous_max");
            Function<ExtendedIOSignalPiece<List<Double>>, List<Double>> expr = visitExtended_expr(ctx.extended_expr());
            return (concreteSignal) -> expr.apply(concreteSignal).stream().max(Double::compare).map(Collections::singletonList).orElse(Collections.emptyList());
        } else if (ctx.PREVIOUS_MIN() != null && ctx.extended_expr() != null) {
            log.trace("previous_min");
            Function<ExtendedIOSignalPiece<List<Double>>, List<Double>> expr = visitExtended_expr(ctx.extended_expr());
            return (concreteSignal) -> expr.apply(concreteSignal).stream().min(Double::compare).map(Collections::singletonList).orElse(Collections.emptyList());
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
    public Function<ExtendedIOSignalPiece<List<Double>>, List<Double>> visitAtomic(net.maswag.ExtendedSignalMapperParser.AtomicContext ctx) {
        if (ctx.signalID != null) {
            int sigIndex = Integer.parseInt(ctx.signalID.getText());
            if (Objects.nonNull(ctx.INPUT())) {
                return (concreteSignal) -> Collections.singletonList(concreteSignal.getInputSignal().get(sigIndex));
            } else if (Objects.nonNull(ctx.OUTPUT())) {
                return (concreteSignal) -> Collections.singletonList(concreteSignal.getOutputSignal().get(sigIndex));
            } else if (Objects.nonNull(ctx.PREVIOUS_MAX_OUTPUT())) {
                return (concreteSignal) -> Collections.singletonList(concreteSignal.getPreviousOutputSignals().stream()
                        // Take the elementwise maximum of the previous output signals
                        .reduce((a, b) -> {
                            List<Double> result = new ArrayList<>();
                            assert a.size() == b.size();
                            for (int i = 0; i < a.size(); i++) {
                                result.add(i, Math.max(a.get(i), b.get(i)));
                            }
                            return result;
                        }).get().get(sigIndex));
            } else { // PREVIOUS_MIN_OUTPUT
                return (concreteSignal) -> Collections.singletonList(concreteSignal.getPreviousOutputSignals().stream()
                        // Take the elementwise minimum of the previous output signals
                        .reduce((a, b) -> {
                            List<Double> result = new ArrayList<>();
                            assert a.size() == b.size();
                            for (int i = 0; i < a.size(); i++) {
                                result.add(i, Math.min(a.get(i), b.get(i)));
                            }
                            return result;
                        }).get().get(sigIndex));
            }
        } else {
            double value = Double.parseDouble(ctx.value().getText());
            return (concreteSignal) -> Collections.singletonList(value);
        }
    }

    @Override
    public Function<ExtendedIOSignalPiece<List<Double>>, List<Double>> visitExtended_expr(Extended_exprContext ctx) {
        if (ctx.OUTPUT() != null) {
            int sigIndex = Integer.parseInt(ctx.signalID.getText());
            return (concreteSignal) -> concreteSignal.getPreviousOutputSignals().stream().map(a -> a.get(sigIndex)).collect(Collectors.toList());
        } if (ctx.left != null && ctx.right != null) {
            // Both left and right are expressions
            return (concreteSignal) -> {
                List<Double> left = visitExtended_expr(ctx.left).apply(concreteSignal);
                List<Double> right = visitExtended_expr(ctx.right).apply(concreteSignal);
                if (ctx.PLUS() != null) {
                    return Streams.zip(left.stream(), right.stream(), Double::sum).collect(Collectors.toList());
                } else if (ctx.MINUS() != null) {
                    return Streams.zip(left.stream(), right.stream(), (a, b) -> a - b).collect(Collectors.toList());
                } else if (ctx.TIMES() != null) {
                    return Streams.zip(left.stream(), right.stream(), (a, b) -> a * b).collect(Collectors.toList());
                } else if (ctx.DIV() != null) {
                    return Streams.zip(left.stream(), right.stream(), (a, b) -> a / b).collect(Collectors.toList());
                } else if (ctx.MIN() != null) {
                    return Streams.zip(left.stream(), right.stream(), Double::min).collect(Collectors.toList());
                } else if (ctx.MAX() != null) {
                    return Streams.zip(left.stream(), right.stream(), Double::max).collect(Collectors.toList());
                } else {
                    throw new UnsupportedOperationException("Unsupported operation");
                }
            };
        } else if (ctx.left != null && ctx.rightv != null) {
            // Left is an expression and right is a value
            double right = Double.parseDouble(ctx.rightv.getText());
            return (concreteSignal) -> {
                List<Double> left = visitExtended_expr(ctx.left).apply(concreteSignal);
                if (ctx.PLUS() != null) {
                    return left.stream().map(a -> a + right).collect(Collectors.toList());
                } else if (ctx.MINUS() != null) {
                    return left.stream().map(a -> a - right).collect(Collectors.toList());
                } else if (ctx.TIMES() != null) {
                    return left.stream().map(a -> a * right).collect(Collectors.toList());
                } else if (ctx.DIV() != null) {
                    return left.stream().map(a -> a / right).collect(Collectors.toList());
                } else if (ctx.MIN() != null) {
                    return Collections.singletonList(left.stream().min(Double::compare).orElse(Double.POSITIVE_INFINITY));
                } else if (ctx.MAX() != null) {
                    return Collections.singletonList(left.stream().max(Double::compare).orElse(Double.NEGATIVE_INFINITY));
                } else {
                    throw new UnsupportedOperationException("Unsupported operation");
                }
            };
        } else if (ctx.leftv != null && ctx.right != null) {
            // Left is a value and right is an expression
            double left = Double.parseDouble(ctx.leftv.getText());
            return (concreteSignal) -> {
                List<Double> right = visitExtended_expr(ctx.right).apply(concreteSignal);
                if (ctx.PLUS() != null) {
                    return right.stream().map(a -> left + a).collect(Collectors.toList());
                } else if (ctx.MINUS() != null) {
                    return right.stream().map(a -> left - a).collect(Collectors.toList());
                } else if (ctx.TIMES() != null) {
                    return right.stream().map(a -> left * a).collect(Collectors.toList());
                } else if (ctx.DIV() != null) {
                    return right.stream().map(a -> left / a).collect(Collectors.toList());
                } else if (ctx.MIN() != null) {
                    return Collections.singletonList(right.stream().min(Double::compare).orElse(Double.POSITIVE_INFINITY));
                } else if (ctx.MAX() != null) {
                    return Collections.singletonList(right.stream().max(Double::compare).orElse(Double.NEGATIVE_INFINITY));
                } else {
                    throw new UnsupportedOperationException("Unsupported operation");
                }
            };
        } else if (ctx.ABS() != null) {
            log.trace("abs");
            assert ctx.extended_expr().size() == 1;
            return (concreteSignal) -> visitExtended_expr(ctx.extended_expr().get(0)).apply(concreteSignal).stream().map(Math::abs).collect(Collectors.toList());
        } else if (ctx.LPAREN() != null) {
            // Paren
            log.trace("paren");
            assert ctx.extended_expr().size() == 1;
            return visitExtended_expr(ctx.extended_expr(0));
        } else {
            throw new UnsupportedOperationException("Unsupported operation");
        }
    }
}
