package net.maswag.falcaun.annotation;

import javax.validation.Constraint;
import javax.validation.Payload;
import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

@Constraint(validatedBy = SortedValidator.class)
@Target({ElementType.TYPE_USE, ElementType.PARAMETER, ElementType.FIELD})
@Retention(RetentionPolicy.RUNTIME)
public @interface Sorted {
    String message() default "The list must be sorted.";
    Class<?>[] groups() default {};
    Class<? extends Payload>[] payload() default {};
}
