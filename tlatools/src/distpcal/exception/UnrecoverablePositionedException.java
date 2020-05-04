package distpcal.exception;

import pcal.AST;

/**
 * @author Simon Zambrovski
 * @version $Id$
 */
public class UnrecoverablePositionedException extends UnrecoverableException
{
    private distpcal.AST position;
    
    public UnrecoverablePositionedException(String message)
    {
        super(message);
    }

    /**
     * @param message
     * @param position
     */
    public UnrecoverablePositionedException(String message, distpcal.AST position)
    {
        super(message);
        this.position = position;
    }
    
    /**
     * @return the elementAt
     */
    public distpcal.AST getPosition()
    {
        return position;
    }

}
