package ElectrumUnitTesting;

import ElectrumUnitTesting.UnitTests.*;
import org.junit.runner.RunWith;
import org.junit.runners.Suite;

@RunWith(Suite.class)
@Suite.SuiteClasses({
        Ring.class,
        Span_tree.class,
        Firewire.class,
        Hotel.class,
        Lift_spl.class
})

public class RunAllSatSolvingUnitTests {
}




