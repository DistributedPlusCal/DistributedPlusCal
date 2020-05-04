package distpcal.exception;

import distpcal.AST;

/**
 * @author Simon Zambrovski
 * @version $Id$
 */
public class DistPcalTranslateException extends UnrecoverablePositionedException
{

    /**
     * @param message
     * @param elementAt2
     */
    public DistPcalTranslateException(String message, AST elementAt2)
    {
        super(message, elementAt2);
    }

    /**
     * @param message
     */
    public DistPcalTranslateException(String message)
    {
        super(message);
    }

}
