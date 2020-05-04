package distpcal.exception;

import distpcal.AST;

/**
 * @author Simon Zambrovski
 * @version $Id$
 */
public class DistPcalTLAGenException extends UnrecoverablePositionedException
{

    /**
     * @param message
     */
    public DistPcalTLAGenException(String message)
    {
        super(message);
    }

    /**
     * @param message
     * @param elementAt2
     */
    public DistPcalTLAGenException(String message, AST elementAt2)
    {
        super(message, elementAt2);
    }
}
