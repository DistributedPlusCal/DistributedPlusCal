package distpcal.exception;

public class ParseDistAlgorithmException extends UnrecoverablePositionedException
{

    /**
     * @param message
     */
    public ParseDistAlgorithmException(String message)
    {
        super(message);
    }

    /**
     * @param string
     * @param elementAt
     */
    public ParseDistAlgorithmException(String message, distpcal.AST elementAt)
    {
        super(message, elementAt);
    }
}
