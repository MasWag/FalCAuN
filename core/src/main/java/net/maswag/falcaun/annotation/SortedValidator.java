package net.maswag.falcaun.annotation;

import javax.validation.ConstraintValidator;
import javax.validation.ConstraintValidatorContext;
import java.util.List;

public class SortedValidator implements ConstraintValidator<Sorted, List<?>> {

    @Override
    public void initialize(Sorted constraintAnnotation) {
    }

    @Override
    public boolean isValid(List<?> list, ConstraintValidatorContext context) {
        if (list == null) {
            return true; // Null is considered valid. Use @NotNull for non-null validation.
        }
        for (int i = 1; i < list.size(); i++) {
            Comparable<Object> prev = (Comparable<Object>) list.get(i - 1);
            Comparable<Object> curr = (Comparable<Object>) list.get(i);
            if (prev.compareTo(curr) > 0) {
                return false;
            }
        }
        return true;
    }
}
