package net.maswag.falcaun;

import de.learnlib.sul.SULMapper;
import lombok.NonNull;

import java.util.List;

public interface ComponentWiseSignalDiscretizer extends SignalDiscretizer {
    /**
     * @return The largest concrete output values for each component
     */
    List<Character> getLargestOutputs();

    /**
     * @return The list of possible abstract output characters for each component
     */
    List<List<Character>> getAbstractOutputs();

    /**
     * SignalDiscretizer pre-composed with an SULMapper.
     */
    default ComponentWiseSignalDiscretizer preCompose(@NonNull SULMapper<List<Double>, IOSignalPiece<List<Double>>, List<Double>, IOSignalPiece<List<Double>>> preMapper) {
        return new PreComposedSignalDiscretizer(this, preMapper);
    }

    /**
     * SignalDiscretizer post-composed with an SULMapper.
     */
    default SignalDiscretizer postCompose(@NonNull SULMapper<String, String, String, String> postMapper) {
        return new PostComposedSignalDiscretizer(this, postMapper);
    }
}
