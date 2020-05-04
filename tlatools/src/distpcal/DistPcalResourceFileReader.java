/***************************************************************************
* CLASS PcalResourceFileReader                                             *
*                                                                          *
* A PcalResourceFileReader returns an object for reading a resource file,  *
* which is a file kept in the same directory as the pcal.AST class.        *
* The constructor takes a file name as argument.  The object's two public  *
* methods are                                                              *
*                                                                           *
*   getLine() : Returns the next line of the file as a string.  Returns    *
*               null after the last line.                                  *
*                                                                          *
*   close()   : Closes the file.                                           *
***************************************************************************/
package distpcal ; 

import java.io.BufferedReader;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.util.Vector;

import distpcal.exception.DistPcalResourceFileReaderException;

public class DistPcalResourceFileReader
  { public DistPcalResourceFileReader(String fileName) throws DistPcalResourceFileReaderException
      /*********************************************************************
      * The constructor, where fileName is the name of a file that's       *
      * in the same directory as pcal.AST.                             *
      *********************************************************************/
     { name = fileName ;
       Class cl = null ;
       
       // TODO fix this!
       try { cl = Class.forName("distpcal.AST"); }
       catch (ClassNotFoundException e)
           { throw new DistPcalResourceFileReaderException( 
               "Java could not find class pcal.AST.  There \n"
             + "    is probably something wrong with the way\n"
             + "    the +cal translator is installed");
           } ;             
       InputStream input = cl.getResourceAsStream(fileName) ; 
       if (input == null)
         { throw new DistPcalResourceFileReaderException( 
               "Could not find resource file " + fileName + ".\n"
             + "    There is probably something wrong with the way\n"
             + "    the +cal translator is installed");
         } ;  
       inputReader = new BufferedReader(new InputStreamReader(input)) ;
      };

  public static Vector<String> ResourceFileToStringVector(String fileName) throws DistPcalResourceFileReaderException
    /***********************************************************************
    * Reads file fileName into a StringVector, a vector in which each      *
    * element is a line of the file.                                       *
    ***********************************************************************/
    { Vector<String> inputVec = new Vector<String>(100) ;
       DistPcalResourceFileReader wordFileReader
                     = new DistPcalResourceFileReader(fileName);

       String word = wordFileReader.getLine();
       while (word != null)
         { inputVec.addElement(word) ;
           word = wordFileReader.getLine() ;
         } ;
       wordFileReader.close();
       return inputVec ;
     }

    public String getLine() throws DistPcalResourceFileReaderException
      /*********************************************************************
      * Returns the next line of input.  After it returns the last line    *
      * of input, it returns null.                                         *
      *********************************************************************/
      { try { return inputReader.readLine();
            }
        catch (java.io.IOException e)
          { throw new DistPcalResourceFileReaderException( 
                   "Error reading the +cal translator resource file " 
                 + name + ".\n"
                 + "    You may be having file system problems");
          }
      }
    private boolean done = false;
      /*********************************************************************
      * If the last line of input doesn't end with a '\n', then getLine()  *
      * returns that line and sets done to true.                           *
      *********************************************************************/

    private BufferedReader inputReader ;
      /*********************************************************************
      * The actual reader for the resource file.                           *
      *********************************************************************/

    private String name ;
      /*********************************************************************
      * A copy of the resource file name, kept for error messages.         *
      *********************************************************************/
      
    public void close() throws DistPcalResourceFileReaderException
      { try { inputReader.close(); }
        catch (java.io.IOException e)
          { throw new DistPcalResourceFileReaderException( 
               "Error trying to close the +cal translator resource file " 
            + name + ".\n"
             + "    You may be having file system problems");
          } ;
      } ;


  }      


/* Last modified on Wed  3 Aug 2005 at 18:41:43 UT by lamport */
