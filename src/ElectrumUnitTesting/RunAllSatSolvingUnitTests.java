package ElectrumUnitTesting;

import ElectrumUnitTesting.UnitTests.Firewire;
import ElectrumUnitTesting.UnitTests.Hotel;
import ElectrumUnitTesting.UnitTests.Ring;
import ElectrumUnitTesting.UnitTests.Span_tree;
import org.junit.runner.RunWith;
import org.junit.runners.Suite;

@RunWith(Suite.class)
@Suite.SuiteClasses({
        Ring.class,
        Span_tree.class,
        Firewire.class,
        Hotel.class
})

public class RunAllSatSolvingUnitTests {
}




