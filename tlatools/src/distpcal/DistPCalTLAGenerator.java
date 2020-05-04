package distpcal;

import java.util.Vector;

import distpcal.exception.DistPcalFixIDException;
import distpcal.exception.DistPcalSymTabException;
import distpcal.exception.DistPcalTLAGenException;
import distpcal.exception.DistPcalTranslateException;
import distpcal.exception.RemoveNameConflictsException;

/**
 * Responsible for generation of TLA+ from PCal AST<br>
 * Note: this class is renamed from NotYetImplemented on 11th March 2009
 * 
 * @author Leslie Lamport, Keith Marzullo
 * @version $Id$
 */
public class DistPCalTLAGenerator
{

    private DistPcalSymTab st = null;
    private AST ast = null; 
             // This is set to the AST constructed by ParseDistAlgorithm.getAlgorithm

    /**
     * Constructs a working copy 
     * @param ast
     */
    public DistPCalTLAGenerator(AST ast)
    {
        this.ast = ast;
    }

    /********************************************************************
     * Called by trans.java.  Should go in a new .java file.            *
     ********************************************************************/
    public void removeNameConflicts() throws RemoveNameConflictsException
    {
        try
        {
            st = new DistPcalSymTab(ast);
        } catch (DistPcalSymTabException e)
        {
            throw new RemoveNameConflictsException(e.getMessage());
        }

        st.Disambiguate();
        if (st.disambiguateReport.size() > 0)
            // SZ March 11, 2009. Warning reporting moved to PCalDebug 
        	DistPcalDebug.reportWarning("symbols were renamed.");
        if (st.errorReport.length() > 0)
            throw new RemoveNameConflictsException(st.errorReport);
        
        try{
            DistPcalFixIDs.Fix(ast, st);
        } catch (DistPcalFixIDException e){
            throw new RemoveNameConflictsException(e.getMessage());
        }
    }

    /********************************************************************
     * The main translation method.  Should go in a new .java file.     *
     * Note that this requires RemoveNameConflicts to be called first   *
     * because of the grotty use of the class variable st.              *
     ********************************************************************/
    public Vector<String> translate() throws RemoveNameConflictsException {
    	Vector<String> result = new Vector<String>();
    	AST xast = null;  // Set to the exploded AST

    	for (int i = 0; i < st.disambiguateReport.size(); i++)
    		result.addElement((String) st.disambiguateReport.elementAt(i));
    	try{
    		xast = DistPcalTranslate.Explode(ast, st);
    	} catch (DistPcalTranslateException e){
    		throw new RemoveNameConflictsException(e);
    	}

    	try{

    		DistPcalTLAGen tlaGenerator = new DistPcalTLAGen();
    		//            result.addAll(tlaGenerator.generate(xast, st));
    		result = tlaGenerator.generate(xast, st, result);
    	} catch (DistPcalTLAGenException e){
    		throw new RemoveNameConflictsException(e);
    	}

    	// tla-pcal debugging
    	/*******************************************************************
    	 * Following test added by LL on 31 Aug 2007.                       *
    	 *******************************************************************/
    	try{
    		if (ParseDistAlgorithm.hasDefaultInitialization){
    			st.CheckForDefaultInitValue();
    		}
    	} catch (DistPcalSymTabException e){
    		throw new RemoveNameConflictsException(e.getMessage());
    	}
    	return result;
    }
}
