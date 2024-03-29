
/***************************************************************************
* CLASS AST                                                                *
*                                                                          *
* This class defines AST objects, which represent non-terminals of the     *
* +CAL grammar, to be subclasses of the AST class.                         *
*                                                                          *
* Each subclass has a toString() method that prints the object as the      *
* TLA+ record that represents that node in the representation of the       *
* abstract syntax tree used in the PlusCal TLA+ specification.             *
*                                                                          *
* There are no explicit classes corresponding to the following             *
* non-terminals.                                                           *
*                                                                          *
*    Algorithm   AlgorithmBody LabelSeq   SimpleStmt   Finalstmt  VarDecls *
*                                                                          *
* However, there are the following classes that do not represent explicit  *
* non-terminals of the +CAL grammar.                                       *
*                                                                          *
* Uniprocess   MultiProcess   SingleAssign   CallReturn   CallGoto         *
*                                                                          *
* Every AST has col and line fields that contain the position of the       *
* first character of the corresponding portion of the algorithm text (as   *
* human ordinals, numbered starting from 1).                               *
*                                                                          *
*                                                                          *
* Since the only way Java has of defining record (struct) type is by       *
* making it a class, all the different AST node subtypes had to be         *
* subclasses.  I didn't want to put each of them in a separate file, so I  *
* made them all nested inner static classes in this file.  (I presume it   *
* doesn't make sense to make them dynamic classes, since that would imply  *
* that each instance of an AST node has its own separate instance of       *
* those classes.  Anyway, we Java produces a runtime NoSuchMethodError     *
* unless I make the inner classes static.)                                 *
*                                                                          *
* To enable a method to figure out what subclass an AST object is, I       *
* initially gave the class a type field and tried to use that field to     *
* determine the type.  However, this didn't work right at all.  The        *
* problem is that when an element of the subtype gets obtained as an       *
* object of the superclass AST--for example, when it's pulled out of a     *
* vector of AST objects, the type field of the resulting object is set to  *
* the value set by the supertype's constructor.  So, I need to actually    *
* find out what Java thinks the class of the object is.  The following     *
* hack seems to work.  To determine if the subclass of an AST object obj   *
* is Skip, one can test                                                    *
*                                                                          *
*    obj.getClass().toString().equals("class pcal.AST$Skip")               *
*                                                                          *
* However, this seems unlikely to work for all versions of all Java        *
* implementations.  So, for each subclass like AST.Skip, we define an      *
* object SkipObj of that class.  We then test if obj is of class AST.Skip  *
* by                                                                       *
*                                                                          *
*    obj.getClass().equals(AST.SkipObj.getClass())                         *
*                                                                          *
* The object SkipObj cannot be declared with an initial value, because     *
* that leads the initialization of the AST class to go into an infinite    *
* loop.  So, the method AST.ASTInit() assign a new AST.Skip node to        *
* AST.SkipObj.                                                             *
*                                                                          *
* I'm sure there's a better way, but I can't find anything about           *
* it in the Java Reference Manual.                                         *
***************************************************************************/
package pcal;
import java.util.Vector;
// For Distributed PlusCal	
import pcal.exception.ParseAlgorithmException;
// end For Distributed PlusCal	

public class AST
  { public static AST.Uniprocess   UniprocessObj   ;
    public static AST.Multiprocess MultiprocessObj ;
    public static AST.Procedure    ProcedureObj    ;
    public static AST.Process      ProcessObj      ;
    public static AST.VarDecl      VarDeclObj      ;
    public static AST.PVarDecl     PVarDeclObj     ;
    public static AST.LabeledStmt  LabeledStmtObj  ;
    public static AST.While        WhileObj        ;
    public static AST.Assign       AssignObj       ;
    public static AST.SingleAssign SingleAssignObj ;
      /*********************************************************************
      * We added an explicit SINGLEASSIGN type to represent a single       *
      * assignment within a multi-assignment.  We did this because Java    *
      * doesn't allow a record (struct) to be constructed as anything      *
      * other than an object of some class.                                *
      *********************************************************************/
    public static AST.Lhs          LhsObj          ;
    public static AST.If           IfObj           ;
    public static AST.Either       EitherObj       ;
    public static AST.With         WithObj         ;
    public static AST.When         WhenObj         ;
    public static AST.PrintS       PrintSObj       ;
    public static AST.Assert       AssertObj       ;
    public static AST.Skip         SkipObj         ;
    public static AST.LabelIf      LabelIfObj      ;
    public static AST.LabelEither  LabelEitherObj  ;
    public static AST.Clause       ClauseObj       ;
      /*********************************************************************
      * Because Java doesn't have records, only objects, we we add an      *
      * explicit Clause object to be a record such that the `clauses'      *
      * field of a LabelEither object is a sequence of Clause objects.     *
      *********************************************************************/
    public static AST.Call         CallObj         ;
    public static AST.Return       ReturnObj       ;
    public static AST.CallReturn   CallReturnObj   ;
    public static AST.CallGoto     CallGotoObj     ;
    public static AST.Goto         GotoObj         ;
    public static AST.Macro        MacroObj        ;
    public static AST.MacroCall    MacroCallObj    ;

    // For Distributed PlusCal	
    public static AST.ChannelSendCall ChannelSenderObj;
    public static AST.ChannelReceiveCall ChannelReceiverObj;
    /**********************************************************************
     * index for fresh variables (for send and receive operations)
     **********************************************************************/
    private static int varIndex = 1;
    /**********************************************************************
     * Constants for the types of channels                               *
     **********************************************************************/
    public static final int CHANNEL_TYPE_UNORDERED = 1;
    public static final int CHANNEL_TYPE_FIFO = 2;
    // end For Distributed PlusCal	

    public int col ;
    public int line ;
      /*********************************************************************
      * These are the column and line numbers of the first token in the    *
      * algorithm text that corresponds to the AST. (They are human        *
      * ordinals, counting from 1.)                                        *
      *********************************************************************/
    public int macroCol  = 0 ;
    public int macroLine = -1 ;  
      /*********************************************************************
      * If this is an object that was inserted into the AST as the result  *
      * of macro expansion, then this is the column and line number of     *
      * the MacroCall object that was expanded.  The col and line values   *
      * give the position of the object in the macro definition that       *
      * yielded the current object when the macro was expanded.            *
      *                                                                    *
      * If the object was not inserted by macro expansion, then macroLine  *
      * equals -1.                                                         *
      *********************************************************************/
    
    /**
     * If this AST is a statement that is the first statement resulting from
     * expansion of a macro call , then macroOriginBegin is set to the  
     * origin.begin value of the macro call.  It is set by 
     * ParseAlgorithm.ExpandMacroCall and is used by PcalTLAGen.GenLabeledStmt 
     * to set the MappingObject.LeftParen that marks the beginning of the 
     * labeled statement's translation.
     * 
     * macroOriginEnd is similarly set for the last statement resulting from
     * the expansion of a mapping call and used to set the labeled statement's
     * translation's MappingObject.RightParen.
     * 
     * This is a Kludge to correct a bug in the TLA+ translation to
     * PlusCal mapping.  These kludges are the result of implementing
     * that mapping on top of the existing translator, rather than rewriting
     * the translation. 
     */
    public PCalLocation macroOriginBegin = null;
    public PCalLocation macroOriginEnd = null;

    public String lbl = "" ;
      /*********************************************************************
      * Added by LL on 3 Mar 2006.  Used to hold a statement's label       *
      * during the parsing process, but irrelevant once the final AST has  *
      * been constructed.                                                  *
      *********************************************************************/
    
    /**
     * If the lbl field is not the empty string "", then lblLocation is
     * the location of the beginning of the label that provided the string
     * if it came from a label written by the user.  It will be null if the
     * label was added by the translator.
     */
    public PCalLocation lblLocation = null ;
    
    /**
     * The region of the PlusCal code from which the object was created.
     */
    private Region origin = null ;
    
    public Region getOrigin() {
        return origin;
    }

    public void setOrigin(Region origin) {
        this.origin = origin;
    }

    public String location()
      /*********************************************************************
      * The string that describes the location in the algorithm of the     *
      * first token that represents the AST object.  Should be used in     *
      * error messages.                                                    *
      *********************************************************************/
      { if (macroLine < 0)
          { return "line " + line + ", column " + col ; }
        else
          { return "line " + line + ", column " + col +
                   " of macro called at line " + macroLine + 
                   ", column " + macroCol ; }
      }
      
    public static void ASTInit()
      /*********************************************************************
      * An initializing method that creates the ...Obj objects used to     *
      * test the class of an AST object.                                   *
      *********************************************************************/
      { UniprocessObj   = new AST.Uniprocess() ;
        MultiprocessObj = new AST.Multiprocess() ;
        ProcedureObj    = new AST.Procedure() ;
        ProcessObj      = new AST.Process() ;
        VarDeclObj      = new AST.VarDecl() ;
        PVarDeclObj     = new AST.PVarDecl() ;
        LabeledStmtObj  = new AST.LabeledStmt() ;
        WhileObj        = new AST.While() ;
        AssignObj       = new AST.Assign() ;
        SingleAssignObj = new AST.SingleAssign() ;
        LhsObj          = new AST.Lhs() ;
        IfObj           = new AST.If() ;
        EitherObj       = new AST.Either() ;
        WithObj         = new AST.With() ;
        WhenObj         = new AST.When() ;
        PrintSObj       = new AST.PrintS() ;
        AssertObj       = new AST.Assert() ;
        SkipObj         = new AST.Skip() ;
        LabelIfObj      = new AST.LabelIf() ;
        LabelEitherObj  = new AST.LabelEither() ;
        CallObj         = new AST.Call() ;
        ReturnObj       = new AST.Return() ;
        CallReturnObj   = new AST.CallReturn() ;
        CallGotoObj     = new AST.CallGoto() ;
        GotoObj         = new AST.Goto() ;
        MacroObj        = new AST.Macro() ;
        MacroCallObj    = new AST.MacroCall() ;
        // For Distributed PlusCal	
        ChannelSenderObj =  new AST.ChannelSendCall();
        ChannelReceiverObj =  new AST.ChannelReceiveCall();
        // end For Distributed PlusCal	
      }


    public static class Uniprocess extends AST
      { public String  name   = "" ;
        public Vector  decls  = null ; // of VarDecl 
        public TLAExpr defs   = null ;
        public Vector  macros = null ; // of Macro
        public Vector  prcds  = null ; // of Procedure
        public Vector  body   = null ; // of LabeledStmt
        public Uniprocess() {};
        public String toString() 
          { return
             Indent(lineCol()) +  
               "[type     |-> \"uniprocess\", " + NewLine() +
               " name  |-> \"" + name + "\", " + NewLine() +
               Indent(" decls  |-> ") + VectorToSeqString(decls) + ","
                                           + 
               EndIndent() + NewLine() +
               Indent(" defs   |-> ") + defs.toString() + ","
                                           + 
               EndIndent() + NewLine() +

              /*************************************************************
              * Uncomment the following to print the macros field.  It is  *
              * commented out so the printed result is what PlusCal.tla    *
              * considers a Uniprocess object to be.                       *
              *************************************************************/
              // Indent(" macros |-> ") + VectorToSeqString(macros) + ","
              //                             + 
              //  EndIndent() + NewLine() +

               Indent(" prcds  |-> ") + VectorToSeqString(prcds) + ","
                                           + 
               EndIndent() + NewLine() +
               Indent(" body  |-> ") + VectorToSeqString(body) + "]" +
               EndIndent() +
            EndIndent() ;
          }
      }

    public static class Multiprocess extends AST
      { public String  name   = "" ;
        public Vector  decls  = null ; // of VarDecl 
        public TLAExpr defs   = null ;
        public Vector  macros = null ; // of Macro
        public Vector  prcds  = null ; // of Procedure
        public Vector  procs  = null ; // of Process
        public Multiprocess() {} ;
        public String  toString() 
          { return
             Indent(lineCol()) +
               "[type    |-> \"multiprocess\", " + NewLine() +
               " name  |-> \"" + name + "\", " + NewLine() +
               Indent(" decls |-> ") + VectorToSeqString(decls) + ","
                                           + 
               EndIndent() + NewLine() +
               Indent(" defs  |-> ") + defs.toString() + ","
                                           + 
               EndIndent() + NewLine() +
              /*************************************************************
              * Uncomment the following to print the macros field.  It is  *
              * commented out so the printed result is what PlusCal.tla    *
              * considers a Multiprocess object to be.                     *
              *************************************************************/
              // Indent(" macros |-> ") + VectorToSeqString(macros) + ","
              //                             + 
              // EndIndent() + NewLine() +

               Indent(" prcds |-> ") + VectorToSeqString(prcds) + ","
                                           + 
               EndIndent() + NewLine() +
               Indent(" procs |-> ") + VectorToSeqString(procs) + "]" +
               EndIndent() +
             EndIndent() ;
          }
      }

    /**
     * The minusLabels and plusLabels fields were added by LL in 
     * January 2011 to implement the Version 1.5 enhancement that allows
     * fairness modifiers on labels.  These Vectors contain the labels
     * in the process that have the indicated modifier.  They are initially
     * set in the GetProcedure method of ParseAlgorithm, with the help of 
     * the GetLabel method.  They are then fixed to correct for label
     * conflicts by the FixProcedure method of PcalFixIDs.
     * 
     * The proceduresCalled field was added later in Jan 2011 by LL because,
     * since procedures can call other procedures, a transitive closure
     * is required to compute the procedures called by a process.  (Those
     * procedures need to be known to compute the fairness conditions, since
     * a fairness requirement on a process implies a fairness requirement on
     * all the procedures that the process calls.)
     * 
     * Note added 2 Apr 2013 by LL.  Also, it should be noted
     * that the transitive closure is computed by the call to PcalFixIDs.Fix,
     * not during the initial parsing phase. 
     * 
     * @author lamport
     *
     */
    public static class Procedure extends AST
      { public String name   = "" ;
        public Vector minusLabels = new Vector();
        public Vector plusLabels = new Vector();
        public Vector proceduresCalled = new Vector();
        public Vector params = null ; // of PVarDecl
        public Vector decls  = null ; // of PVarDecl 
        public Vector body   = null ; // of LabeledStmt
        public Procedure() {} ;
        public String toString() 
          { 
            // For versions earlier than 1.5 need to return those versions'
            // value since toString() is used to generate the AST module
            // used when TLC is doing the translation.
            if (PcalParams.inputVersionNumber < PcalParams.VersionToNumber("1.5")){
              return
                Indent(lineCol()) +
                  "[name   |-> \"" + name + "\", " + NewLine() +
                  Indent(" params |-> ") + VectorToSeqString(params) + "," + 
                  EndIndent() + NewLine() +
                  Indent(" decls  |-> ") + VectorToSeqString(decls) + "," + 
                  EndIndent() + NewLine() +
                  Indent(" body   |-> ") + VectorToSeqString(body) + "]" +
                  EndIndent() + 
                EndIndent() ;
            } 
            return
             Indent(lineCol()) +
               "[name   |-> \"" + name + "\", " + NewLine() +
               "minusLabels |-> "
               + VectorToSeqQuotedString(minusLabels) + ", plusLabels |->"
               + VectorToSeqQuotedString(plusLabels) + ", proceduresCalled |->"
               + VectorToSeqQuotedString(proceduresCalled) + ","
             + NewLine() +
               Indent(" params |-> ") + VectorToSeqString(params) + "," + 
               EndIndent() + NewLine() +
               Indent(" decls  |-> ") + VectorToSeqString(decls) + "," + 
               EndIndent() + NewLine() +
               Indent(" body   |-> ") + VectorToSeqString(body) + "]" +
               EndIndent() + 
             EndIndent() ;
          }
      }
    
    /***********************************************************************
    * Constants used to describe a process's fairness assumption.          *
    ***********************************************************************/
    public static final int UNFAIR_PROC = 0;
    public static final int WF_PROC = 1;
    public static final int SF_PROC = 2;
    public static final String[] FairnessString = {"unfair", "wf", "sf"} ;
    
    /**
     * The minusLabels and plusLabels fields were added by LL in 
     * January 2011 to implement the Version 1.5 enhancement that allows
     * fairness modifiers on labels.  They are set much like the corresponding
     * fields of an AST.Procedure object, as described above.
     * The proceduresCalled field was also added then.  
     * 
     * Note added by LL on 2 April 2013.  The genius LL never noticed that 
     * the proceduresCalled field only contains the procedures directly called,
     * and he used that in generating the fairness conditions without finding
     * the procedures that are called indirectly.
     * 
     * @author lamport
     *
     */
    public static class Process extends AST
      { public String    name  = "" ;
        public int fairness = UNFAIR_PROC ;
        public Vector  minusLabels = new Vector();
        public Vector  plusLabels = new Vector();
        public Vector  proceduresCalled = new Vector();
        public boolean   isEq  = true ; // true means "=", false means "\\in"
        public TLAExpr   id    = null ;
        public Vector    decls = null ; // of VarDecl
        public Vector    body  = null ; // of LabeledStmt
        // For Distributed PlusCal	
        public Vector<Thread> threads = null;
        // end For Distributed PlusCal	
        public Process() { };
        public String toString() 
          { 
            // For versions earlier than 1.5 need to return those versions'
            // value since toString() is used to generate the AST module
            // used when TLC is doing the translation.
            if (PcalParams.inputVersionNumber < PcalParams.VersionToNumber("1.5")){
              return
               Indent(lineCol()) +
                 "[name   |-> \"" + name + "\", " + NewLine() +
                 " eqOrIn |-> " + boolToEqOrIn(isEq) + "," + NewLine() +
                 " id     |-> " + id.toString() + "," + NewLine() +
                 Indent(" decls  |-> ") + 
                    VectorToSeqString(decls) + "," + 
                 EndIndent() + NewLine() +
               // For Distributed PlusCal
              ((body != null) ?
               Indent(" body   |-> ") + VectorToSeqString(body) + "]" :
               Indent(" threads   |-> ") + VectorToSeqString(threads) + "]" ) +
               // end For Distributed PlusCal
                 EndIndent() + 
              EndIndent() ;
            } 
            
            return
             Indent(lineCol()) +
               "[name   |-> \"" + name + "\"," 
               + NewLine() +
               " fairness |-> \"" 
                 + FairnessString[fairness] + "\", minusLabels |-> "
                 + VectorToSeqQuotedString(minusLabels) + ", plusLabels |->"
                 + VectorToSeqQuotedString(plusLabels) + ", proceduresCalled |->"
                 + VectorToSeqQuotedString(proceduresCalled) + ","
               + NewLine() +
               " eqOrIn |-> " + boolToEqOrIn(isEq) + "," + NewLine() +
               " id     |-> " + id.toString() + "," + NewLine() +
               Indent(" decls  |-> ") + 
                  VectorToSeqString(decls) + "," + 
               EndIndent() + NewLine() +
               // For Distributed PlusCal
              ((body != null) ?
               Indent(" body   |-> ") + VectorToSeqString(body) + "]" :
               Indent(" threads   |-> ") + VectorToSeqString(threads) + "]" ) +
               // end For Distributed PlusCal	
               EndIndent() + 
             EndIndent() ;
          }
     }

    public static class VarDecl extends AST
      { public String    var  = null ;
        public boolean   isEq = true ; // true means "=", false means "\\in"
        public TLAExpr   val  = PcalParams.DefaultVarInit();
        public VarDecl() {};
        public String toString() 
          { return 
             Indent(lineCol()) + 
                    "[var |-> \"" + var + "\", " + 
                    "eqOrIn |-> " + boolToEqOrIn(isEq) + ", " +
                    "val |-> " + val.toString() + "]" + 
             EndIndent() ;
          }
      }

    public static class PVarDecl extends AST
      { public final boolean isEq = true    ;  // true means "="
        public String        var  = null ;
        public TLAExpr       val  = PcalParams.DefaultVarInit();
        public PVarDecl() {};
        
        /**
         * Converts the PVarDecl object to an equivalent VarDecl
         * object.  (I don't know why I bothered introducing a separate
         * PVarDecl object in the first place.)
         * @return
         */
        public VarDecl toVarDecl() {
            VarDecl result = new VarDecl() ;
            result.var = this.var ;
            result.val = this.val ;
            result.setOrigin(this.getOrigin());
            result.isEq = true ;
            return result ;
        }
        
        public String toString() 
          { return 
             Indent(lineCol()) + 
                    "[var |-> \"" + var + "\", " + 
                    "eqOrIn |-> \"=\", " +
                    "val |-> " + val.toString() + "]"  + 
             EndIndent() ;
          }
      }

    public static class LabeledStmt extends AST
      { public String    label = null ;
        public Vector    stmts = null ;  
          /*****************************************************************
          * An optional While prepended to a LabelSeq.                     *
          *****************************************************************/

        public LabeledStmt() { } ;
        public String toString() 
          {return 
             Indent(lineCol()) + 
                    "[label |-> \"" + label + "\"," + NewLine() +
                    Indent(" stmts |-> ") + 
                     VectorToSeqString(stmts) + "]" +  
                    EndIndent() +
             EndIndent() ;
          }
     }   


    public static class While extends AST
      { public TLAExpr   test    = null ;
        public Vector    unlabDo = null ; // a LabelSeq
        public Vector    labDo   = null ; // of LabeledStmt 
        public While() { };
        public String toString() 
          { return 
             Indent(lineCol()) + 
                "[type    |-> \"while\", " + NewLine() +
                " test    |-> " + test.toString()  +  "," + NewLine() +
                Indent(" labDo   |-> ") +
                    VectorToSeqString(labDo) + ","  + 
                EndIndent() + NewLine() +
                
                Indent(" unlabDo |-> ") +
                    VectorToSeqString(unlabDo) + "]" +
                EndIndent() + 
             EndIndent() ;
          }
      }


    public static class Assign extends AST
      { public Vector    ass  = null ; // of SingleAssign
        public Assign() { } ;
        public String toString()
          { return 
              Indent(lineCol()) +
                "[type |-> \"assignment\"," + NewLine() +
                Indent(" ass  |-> ") +
                     VectorToSeqString(ass) + "]" +
                EndIndent() +
              EndIndent() ;
          }
      }

    public static class SingleAssign extends AST
      { public Lhs       lhs  = new Lhs() ; 
        public TLAExpr   rhs  = null ; 
        public SingleAssign() { };
        public String toString()
          { return 
            Indent(lineCol()) + 
              "[lhs |-> " + lhs.toString() + "," + NewLine() +
              " rhs |-> " + rhs.toString() + "]"  +
            EndIndent() ;
          }
      }

    public static class Lhs extends AST
      /*********************************************************************
      * Note use of Lhs as name rather than LHS, which is the type         *
      * constant.                                                          *
      *********************************************************************/
      { public String    var  = "" ;
        public TLAExpr   sub  = null ; 
        public Lhs() { };
        public String toString()
          { return lineCol() + 
                   "[var |-> \"" + var + "\", sub |-> " 
                    + sub.toString() + "]"; }
      }

    /**
     * An AST.If object is created from an AST.LabelIf or AST.While object.
     * For a LabelIf containing no labeled statements, it is created inside
     * the CheckLabeledStmtSeq method when executing ParseAlgorithm.runMe(String[]).
     * Otherwise, it is created by exploding the original AST inside the
     * call of  PcalFixIDs.Fix.  Its origin is set to that of the original AST.
     * 
     * @author lamport
     *
     */
    public static class If extends AST
      { public TLAExpr   test = null ;
        public Vector    Then = null ; // of SimpleStmt
          /*****************************************************************
          * Could use "then", but use "Then" to avoid confusion since we   *
          * can't use "else".                                              *
          *****************************************************************/
        public Vector    Else = null ; // of SimpleStmt
          /*****************************************************************
          * Can't use "else" because that's a Java keyword.                *
          *****************************************************************/
        
        public static final int UNBROKEN     = 0 ;
        public static final int BROKEN_WHILE = 1;
        public static final int BROKEN_THEN  = 2;
        public static final int BROKEN_ELSE  = 4;
        /**
         * The source field records the information about where the If came
         * from that is useful for the TLA+ to PlusCal translation.  The values
         * are:
         * 
         *   UNBROKEN : Contains the entire contents of the original AST.
         *   BROKEN_WHILE : Came from a While containing a labeled statement.
         *   BROKEN_THEN : Came from an IfThen that contained a labeled statement
         *      in the Then clause, but not the Else clausew.
         *   BROKEN_ELSE : Came from an IfThen that contained a labeled statement
         *      in the Else clause but not the Then clause.
         *   BROKEN_THEN + BROKEN_ELSE : Came from an IfThen with labeled statements
         *      in both clauses.     
         */
        private int source = UNBROKEN ;
        public int getSource() {
            return source;
        }
        public void setSource(int source) {
            this.source = source;
        }

        public If() { };
        public String toString()
          { return 
             Indent(lineCol()) + 
                "[type    |-> \"if\", " + NewLine() +  
                " test    |-> " + test.toString() + "," + NewLine() +
                Indent(" then |-> ") + VectorToSeqString(Then) + "," 
                                          + 
                EndIndent() + NewLine() +
                Indent(" else |-> ") + VectorToSeqString(Else) + "]" + 
                EndIndent() +
             EndIndent() ; 
           }
      }     

    public static class Either extends AST
      { public Vector ors = null ; // of Seq(SimpleStmt)
        public Either() { };
        public String toString()
          { return 
             Indent(lineCol()) + 
                "[type |-> \"either\", " + NewLine() +  
                Indent(" ors  |-> ") + VectorOfVectorsToSeqString(ors) + "]" + 
                EndIndent() +
             EndIndent() ; 
          }
      }

    public static class With extends AST
      { public String    var  = "" ;
        public boolean   isEq = true ; // true means "=", false "\\in"
        public TLAExpr   exp  = null ;
        public Vector    Do   = null ; // of SimpleStmt
          /*****************************************************************
          * Can't use "do" because that's a Java keyword.                  *
          *****************************************************************/
        public With() { };
        public String toString()
          { return
             Indent(lineCol()) + 
               "[type   |-> \"with\", " + NewLine() + 
               " var    |-> \"" + var + "\"," + NewLine() + 
               " eqOrIn |-> " + boolToEqOrIn(isEq) + ","  + NewLine() + 
               " exp    |-> " + exp.toString() + "," + NewLine() +          
               Indent(" do     |-> ") + VectorToSeqString(Do) + "]" + 
               EndIndent() +
             EndIndent() ;
          }
      }

    public static class When extends AST
      { public TLAExpr   exp  = null ;
        public When() {};
        public String toString()
          { return 
             Indent(lineCol()) + 
              "[type |-> \"when\", " + NewLine() + 
              " exp |-> " + exp.toString() + "]" +
             EndIndent() ;
          }
      }

    public static class PrintS extends AST
      { public TLAExpr   exp  = null ;
        public PrintS() { };
        public String toString()
          { return 
             Indent(lineCol()) + 
              "[type |-> \"print\", " + NewLine() + 
              " exp |-> " + exp.toString() + "]" +
             EndIndent() ;
          }
      }

    public static class Assert extends AST
      { public TLAExpr   exp  = null ;
        public Assert() {};
        public String toString()
          { return 
             Indent(lineCol()) + 
              "[type |-> \"assert\", " + NewLine() + 
              " exp |-> " + exp.toString() + "]" +
             EndIndent() ;
          }
      }

    public static class Skip extends AST
      { 
        public Skip() {};
        public String toString()
          { return lineCol() + "[type |-> \"skip\"]";
          }
      }


    /**
     * A LabelIf represents an if statement whose then and/or
     * else clause has a label.
     * 
     * @author lamport
     *
     */
    public static class LabelIf extends AST
      { public TLAExpr   test      = null ;
        public Vector    unlabThen = null ; // a LabelSeq
        public Vector    labThen   = null ; // of LabeledStmt 
        public Vector    unlabElse = null ; // a LabelSeq
        public Vector    labElse   = null ; // of LabeledStmt 
        public LabelIf() { };
        public String toString()
          { return 
             Indent(lineCol()) + 
               "[type      |-> \"labelIf\"," + NewLine() +
               " test      |-> " + test.toString() + "," + NewLine() +
               Indent(" unlabThen |-> ") + VectorToSeqString(unlabThen) 
                                           + "," + 
               EndIndent() + NewLine() +
               Indent(" labThen   |-> ") + VectorToSeqString(labThen) 
                                            + "," + 
               EndIndent() + NewLine() +
               Indent(" unlabElse |-> ") + VectorToSeqString(unlabElse) 
                                             + "," + 
               EndIndent() + NewLine() +
               Indent(" labElse   |-> ") + VectorToSeqString(labElse) 
                                             + "]" + 
               EndIndent() + NewLine() +
             EndIndent() ;
          }
      }

    public static class LabelEither extends AST
      { public Vector    clauses = null ; // of Clause
        public LabelEither() { };
        public String toString()
          { return 
             Indent(lineCol()) + 
               "[type    |-> \"labelEither\"," + NewLine() +
               Indent(" clauses |-> ") + VectorToSeqString(clauses) 
                                             + "]" + 
               EndIndent() + NewLine() +
             EndIndent() ;
          }
      }

    public static class Clause extends AST
      { public Vector    unlabOr = null ; // a LabelSeq
        public Vector    labOr   = null ; // LabeledStmt

        public Clause() {   
        }
        
        /**
         * The broken field is true iff the Clause object came from
         * a LabelEither object for which the corresponding clause
         * contained a labeled statement. 
         */
        private boolean broken = false ;
        public boolean isBroken() {
            return broken;
        }

        public void setBroken(boolean broken) {
            this.broken = broken;
        }

        public String toString()
          { return 
             Indent(lineCol()) +
               Indent("[unlabOr |-> ") + VectorToSeqString(unlabOr) 
                                           + "," + 
               EndIndent() + NewLine() +
               Indent(" labOr   |-> ") + VectorToSeqString(labOr) 
                                            + "]" + 
               EndIndent() + NewLine() +
             EndIndent() ;
          }
      }

    public static class Call extends AST
      { public String    returnTo = "" ;
        public String    to       = "" ;
        public Vector    args     = null ; // of TLAExpr
        public Call() {};
        public String toString()
          { return 
             Indent(lineCol()) + 
               "[type     |-> \"call\"," + NewLine() +
               " returnTo |-> \"" + returnTo + "\"," + NewLine() +
               " to       |-> \"" + to + "\"," + NewLine() +
               Indent(" args     |-> ") + VectorToSeqString(args) + "]" +
               EndIndent() +
             EndIndent() ;
          }
      }

    public static class Return extends AST
      { public String    from = "" ;
        public Return() {};
        public String toString()
          { return 
              lineCol() + 
               "[type |-> \"return\", from |-> \"" + from + "\"]" ;
          }
      }

    /**
     * A CallReturn object represents a call immediately followed
     * by a return.
     * 
     * @author lamport
     *
     */
    public static class CallReturn extends AST
      { public String    from = "" ;
        public String    to       = "" ;
        public Vector    args     = null ; // of TLAExpr
        public CallReturn() { };
        public String toString()
          { return 
             Indent(lineCol()) + 
               "[type     |-> \"callReturn\"," + NewLine() +
               " from     |-> \"" + from + "\"," + NewLine() +
               " to       |-> \"" + to + "\"," + NewLine() +
               Indent("args     |-> ") + VectorToSeqString(args) 
                                             + "]" + NewLine() +
               EndIndent() +
             EndIndent() ;
          }
      }

    public static class CallGoto extends AST
      { public String    after = "" ;
        public String    to       = "" ;
        public Vector    args     = null ; // of TLAExpr
        public CallGoto() { };
        public String toString()
          { return 
             Indent(lineCol()) + 
               "[type     |-> \"callGoto\"," + NewLine() +
               " after    |-> \"" + after + "\"," + NewLine() +
               " to       |-> \"" + to + "\"," + NewLine() +
               Indent("args     |-> ") + VectorToSeqString(args) 
                                             + "]" + NewLine() +
               EndIndent() +
             EndIndent() ;
          }
      }

    public static class Goto extends AST
      { public String    to       = "" ;
        public Goto() {};
        public String toString()
          { return 
             lineCol() + 
               "[type |-> \"goto\", " + 
               " to |-> \"" + to + "\"]" ;
          }
      }

    public static class Macro extends AST
      { public String name   = "" ;
        public Vector params = null ; // of Strings
        public Vector body   = null ; // of Stmt
        public Macro() {};
        public String toString()
          { return 
             Indent(lineCol()) +
               "[name   |-> \"" + name + "\", " + NewLine() +
               Indent(" params |-> ") + VectorToSeqString(params) + "," + 
               EndIndent() + NewLine() +
               Indent(" body   |-> ") + VectorToSeqString(body) + "]" +
               EndIndent() + 
             EndIndent() ;
          }
      }

    public static class MacroCall extends AST
      { public String name   = "" ;
        public Vector args     = null ; // of TLAExpr
        public MacroCall() {};
        public String toString()
          { return 
             Indent(lineCol()) + 
               "[type |-> \"macrocall\"," + NewLine() +
               " name |-> \"" + name + "\"," + NewLine() +
               Indent(" args     |-> ") + VectorToSeqString(args) + "]" +
               EndIndent() +
             EndIndent() ;
          }
      }

/***************************** UTILITY METHODS ****************************/

   public String boolToEqOrIn(boolean iseq)
     { if (iseq)
         { return "\"=\"" ;}
       else
         { return "\"\\\\in\"" ;} 
     }

   public String lineCol() 
     /**********************************************************************
     * Equals "(*line, col*)" if pcal.trans called in debugging mode,      *
     * otherwise the empty string.                                         *
     **********************************************************************/
     { if (PcalParams.Debug)
         { return "(*" + line + ", " + col +"*)" ;
         }
       else 
         { return "" ;}
     }

   /************************************************************************
   * Methods for getting the toString() methods to indent the              *
   * representation nicely so it's readable.  They are used as follows.    *
   * Suppose we are printing a record with fields foo, foobar, elf, and    *
   * we want it to be output as:                                           *
   *                                                                       *
   *    [foo |-> XXXXXX                                                    *
   *             XXXXXX                                                    *
   *             XXXXX ,                                                   *
   *     elf    |-> "elf",                                                 *
   *     foobar |-> YYYY                                                   *
   *                YYY ]                                                  *
   *                                                                       *
   * where XX...XXX is produced by XXX.toString and YY...YYY by            *
   * YYY.toString().  We would produce the string as follows:              *
   *                                                                       *
   *    Indent("[foo |-> ") +                                              *
   *           XXX.toString() + "," +                                      *
   *    EndIndent() + NewLine() +                                          *
   *    "[elf    |-> \"elf\"," + NewLine()                                 *
   *    NewLine() +                                                        *
   *    Indent(" foobar |-> ") +                                           *
   *             XXX.toString() + "]" +                                    *
   *    EndIndent()                                                        *
   ************************************************************************/
   public static int indentDepth = 0 ;
   public static int[] curIndent = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
                                    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
                                    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
                                    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
                                    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
                                    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
                                    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
                                    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
                                    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 } ;
     /**********************************************************************
     * There must be an easier way.                                        *
     **********************************************************************/
     
   public static String Indent(String str)
     { curIndent[indentDepth + 1] = curIndent[indentDepth] + str.length() ;
       indentDepth = indentDepth + 1 ;
       return str ;
     }

   public static String EndIndent()
     { indentDepth = indentDepth - 1 ;
       return "" ;
     }


   public static String NewLine()
     { String result = "\n" ;
       int i = 0 ;
       while (i < curIndent[indentDepth])
         { result = result + " " ;
           i = i + 1 ;
         } ;
       return result ;
     }     

     
   public static String VectorToSeqString(Vector vec)
     /**********************************************************************
     * Returns the TLA+ representation of vec as a sequence of its         *
     * elements, where toString() is used to produce the elements'         *
     * representation.                                                     *
     **********************************************************************/
     { if (vec == null) {return "null" ;} ;
       String result = Indent("<<") ;
       int i = 0 ;
       while (i < vec.size())
         { if (i > 0)
             { result = result + ", " + NewLine() ; } ;
           result = result + vec.elementAt(i).toString() ;
           i = i + 1 ;
         } ;
       return result + ">>" + EndIndent();
     }
   
   public static String VectorToSeqQuotedString(Vector vec)
   /**********************************************************************
   * Returns the TLA+ representation of vec as a sequence of quoted      *
   * elements, where toString() is used to produce the elements'         *
   * representation to be quoted.                                        *
   **********************************************************************/
   { if (vec == null) {return "null" ;} ;
     String result = Indent("<<") ;
     int i = 0 ;
     while (i < vec.size())
       { if (i > 0)
           { result = result + ", " /* + NewLine() */ ; } ;
         result = result + "\"" + vec.elementAt(i).toString() + "\"" ;
         i = i + 1 ;
       } ;
     return result + ">>" + EndIndent();
   }

   public static String VectorOfVectorsToSeqString(Vector vecvec)
     /**********************************************************************
     * Returns the TLA+ representation of vec as a sequence of its         *
     * elements, where each of its elements is a vector of objects whose   *
     * representation is obtained by calling toString().                   *
     **********************************************************************/
     { String result = Indent("<< ") ;
       int i = 0 ;
       while (i < vecvec.size())
         { if (i > 0)
             { result = result + ", " + NewLine() ; } ;
           result = result + VectorToSeqString((Vector) vecvec.elementAt(i));
           i = i + 1 ;
         } ;
       return result + " >>" + EndIndent();
     }
      
   // For Distributed PlusCal
   public static class Channel extends VarDecl{
     public Vector dimensions;
     public int channelType;     

     public Channel(int channelType) {
       dimensions = new Vector(); // of Strings, the domains for each dimension
       this.channelType = channelType;
     };

     public Vector send(TLAExpr msg, TLAExpr callExp) {
       Channel channel = this;
       String channelName = this.var;
       Vector result = new Vector();

       if(! (channelType == CHANNEL_TYPE_UNORDERED
          || channelType == CHANNEL_TYPE_FIFO) ) {
            PcalDebug.ReportBug("Unexpected channel type.");
            return null;
       }
       
       AST.SingleAssign sass = new AST.SingleAssign();
       sass.line = line;
       sass.col  = col;
       sass.lhs.var = channel.var;
       
       TLAExpr expr = new TLAExpr();
       
       if(callExp.tokens != null) {
         sass.lhs.sub = callExp.cloneAndNormalize();
       }else {
         sass.lhs.sub = new TLAExpr(new Vector());
       }
       
       expr.addLine();
       
       String prevChannel = (channel.dimensions.size() == 0)  ? channelName : "@";
       
       if(channelType == CHANNEL_TYPE_UNORDERED) {
         if(PcalParams.setChannels){
           expr.addToken(PcalTranslate.BuiltInToken(prevChannel));
           expr.addToken(PcalTranslate.BuiltInToken(" \\cup "));
           expr.addToken(PcalTranslate.BuiltInToken("{"));
         } else { // bag
           expr.addToken(PcalTranslate.BuiltInToken(prevChannel));
           expr.addToken(PcalTranslate.BuiltInToken(" (+) "));
           // expr.addToken(PcalTranslate.BuiltInToken("["));
           // String freshVar = "__v" + varIndex++ + "__";
           // expr.addToken(PcalTranslate.BuiltInToken(freshVar));
           // expr.addToken(PcalTranslate.BuiltInToken(" \\in "));
           // expr.addToken(PcalTranslate.BuiltInToken("{"));
           expr.addToken(PcalTranslate.IdentToken("SetToBag"));
           expr.addToken(PcalTranslate.BuiltInToken("("));
           expr.addToken(PcalTranslate.BuiltInToken("{"));        
         }
       } else if(channelType == CHANNEL_TYPE_FIFO) {
         expr.addToken(PcalTranslate.BuiltInToken(" Append("));
         expr.addToken(PcalTranslate.BuiltInToken(prevChannel));
         expr.addToken(PcalTranslate.BuiltInToken(", "));
       }
       // insert the message part
       for(int i = 0; i < msg.tokens.size(); i++) {
         Vector tv = (Vector) msg.tokens.elementAt(i);
         for (int j = 0; j < tv.size(); j++) {
           TLAToken tok = (TLAToken) tv.elementAt(j);
           expr.addToken(tok);
         }
       }
       if(channelType == CHANNEL_TYPE_UNORDERED) {
         if(PcalParams.setChannels){
           expr.addToken(PcalTranslate.BuiltInToken("}"));
         } else { // bag
           expr.addToken(PcalTranslate.BuiltInToken("}"));
           // expr.addToken(PcalTranslate.BuiltInToken(" |-> "));
           // expr.addToken(PcalTranslate.BuiltInToken("1"));
           // expr.addToken(PcalTranslate.BuiltInToken("]"));
           expr.addToken(PcalTranslate.BuiltInToken(")"));
         }
       } else if(channelType == CHANNEL_TYPE_FIFO) {
         expr.addToken(PcalTranslate.BuiltInToken(")"));
       }
       expr.normalize();
       sass.rhs = expr;
       sass.setOrigin(this.getOrigin());
       
       AST.Assign assign = new AST.Assign();
       assign.ass = new Vector();
       assign.line = line ;
       assign.col  = col ;
       assign.setOrigin(this.getOrigin());
       
       assign.ass.addElement(sass);
       
       result.addElement(assign);
       
       return result;
     }
     
     public Vector receive(VarDecl targetVar, TLAExpr callExp, TLAExpr targetExp){    
       if(channelType == CHANNEL_TYPE_UNORDERED) {
         return receiveForUnorderedChannel(targetVar, callExp, targetExp);
       } else if(channelType == CHANNEL_TYPE_FIFO) {
         return receiveForFifoChannel(targetVar, callExp, targetExp);
       } else {
         PcalDebug.ReportBug("Unexpected channel type.");
         return null;
       }
     }

     private Vector receiveForUnorderedChannel(VarDecl targetVar, TLAExpr callExp, TLAExpr targetExp) {
       Channel channel = this;
       String channelName = this.var;
       Vector result = new Vector();
       
       TLAExpr exp = new TLAExpr();
       
       String freshVar = "__" + channelName.toLowerCase().charAt(0) + varIndex++ + "__";
       // with freshVar \in chanName[dim] do <assign>
       AST.With with = new AST.With();
       with.col = line;
       with.line = col;
       with.var = freshVar;
       with.isEq = false;
       // chanName[dim]
       exp = new TLAExpr();
       exp.addLine();
       if(!PcalParams.setChannels){ // bag
         exp.addToken(PcalTranslate.BuiltInToken("DOMAIN "));
       } 
       exp.addToken(PcalTranslate.IdentToken(channelName));
       if(callExp.tokens != null) {
         for(int i = 0; i < callExp.tokens.size(); i++) {
           Vector tv = (Vector) callExp.tokens.elementAt(i);
           for (int j = 0; j < tv.size(); j++) {
             TLAToken tok = (TLAToken) tv.elementAt(j);
             exp.addToken(tok);
           }
         }
       }
       exp.normalize();
       with.exp = exp;
       with.setOrigin(this.getOrigin());
       // assign = <sass1> + <sass2>
       AST.Assign assign = new AST.Assign();
       assign.ass = new Vector();
       assign.line = line ;
       assign.col  = col ;
       assign.setOrigin(this.getOrigin());
       // sass1 = targetVar := freshVar
       AST.SingleAssign sass = new AST.SingleAssign();
       sass.line = line;
       sass.col  = col;
       // targetVar
       sass.lhs.var = targetVar.var;
       sass.lhs.sub = targetExp.cloneAndNormalize();
       // freshVar (which represents an element in the domain of the bag, thus of arity > 0)
       TLAExpr expr = new TLAExpr();
       expr.addLine();
       expr.addToken(PcalTranslate.IdentToken(freshVar));
       expr.normalize();
       sass.rhs = expr;
       sass.setOrigin(this.getOrigin());
       // set sass1
       assign.ass.addElement(sass);
       // sass2 = chanName[dim] :=
       sass = new AST.SingleAssign();
       sass.line = line;
       sass.col  = col;
       // chanName[dim]
       sass.lhs.var = channelName;
       if(callExp.tokens != null) {
         sass.lhs.sub = callExp.cloneAndNormalize();
       }else {
         sass.lhs.sub = new TLAExpr(new Vector());
       }
       // chanName/@  (-) SetToBag({message})
       // alternative: chanName/@  (-) [fv \in {message} |-> 1]
       // for set implementation: chanName/@ \ { freshVar }
       expr = new TLAExpr();
       expr.addLine();
       String prevChannel = (channel.dimensions.size() == 0) ? channelName : "@";
       expr.addToken(PcalTranslate.BuiltInToken(prevChannel)); 
       
       if(PcalParams.setChannels){
         expr.addToken(PcalTranslate.BuiltInToken(" \\ "));
         expr.addToken(PcalTranslate.BuiltInToken("{"));
         expr.addToken(PcalTranslate.IdentToken(freshVar));
         expr.addToken(PcalTranslate.BuiltInToken("}"));
       } else { // bag
         expr.addToken(PcalTranslate.BuiltInToken(" (-) "));
         // expr.addToken(PcalTranslate.BuiltInToken("["));
         // String localFreshVar = "__v" + varIndex++ + "__";
         // expr.addToken(PcalTranslate.BuiltInToken(localFreshVar));
         // expr.addToken(PcalTranslate.BuiltInToken(" \\in "));
         expr.addToken(PcalTranslate.IdentToken("SetToBag"));
         expr.addToken(PcalTranslate.BuiltInToken("("));
         // message variable
         expr.addToken(PcalTranslate.BuiltInToken("{"));
         expr.addToken(PcalTranslate.IdentToken(freshVar));
         expr.addToken(PcalTranslate.BuiltInToken("}"));
         // expr.addToken(PcalTranslate.BuiltInToken(" |-> "));
         // expr.addToken(PcalTranslate.BuiltInToken("1"));
         // expr.addToken(PcalTranslate.BuiltInToken("]"));
         expr.addToken(PcalTranslate.BuiltInToken(")"));
       }
       expr.normalize();
       sass.rhs = expr;
       sass.setOrigin(this.getOrigin());
       // set sass2
       assign.ass.addElement(sass);
       // set body for With
       Vector doBody = new Vector();
       doBody.addElement(assign);
       with.Do = doBody;
       // set result
       result.addElement(with);
       
       return result;
     }
     
     private Vector receiveForFifoChannel(VarDecl targetVar, TLAExpr callExp, TLAExpr targetExp) {
       Channel channel = this;
       String channelName = this.var;
       Vector result = new Vector();
       
       TLAExpr exp = new TLAExpr();
       
       // when (Len(chanName[dim]) > 0) <headAssign> <tailAssign>
       AST.When when = new AST.When();
       when.col = line;
       when.line = col;
       // Len(chanName[dim]) > 0
       exp = new TLAExpr();
       exp.addLine();
       exp.addToken(PcalTranslate.BuiltInToken("Len("));
       exp.addToken(PcalTranslate.IdentToken(channelName));
       if(callExp.tokens != null) {
         for(int i = 0; i < callExp.tokens.size(); i++) {
           Vector tv = (Vector) callExp.tokens.elementAt(i);
           for (int j = 0; j < tv.size(); j++) {
             TLAToken tok = (TLAToken) tv.elementAt(j);
             exp.addToken(tok);
           }
         }
       }
       exp.addToken(PcalTranslate.BuiltInToken(") > 0 "));
       exp.normalize();
       when.exp = exp;
       when.setOrigin(this.getOrigin());
       // <headAssign> = targetVar := Head(chanName[dim])
       AST.Assign headAssign = new AST.Assign();
       headAssign.ass = new Vector();
       headAssign.line = line ;
       headAssign.col  = col ;
       headAssign.setOrigin(this.getOrigin());
       // targetVar
       AST.SingleAssign sass = new AST.SingleAssign();
       sass.line = line;
       sass.col  = col;
       sass.lhs.var = targetVar.var;
       sass.lhs.sub = targetExp.cloneAndNormalize();
       // Head(chanName[dim])
       TLAExpr expr = new TLAExpr();
       expr.addLine();
       expr.addToken(PcalTranslate.BuiltInToken("Head("));
       expr.addToken(PcalTranslate.IdentToken(channelName));
       if(callExp.tokens != null) {
         for(int i = 0; i < callExp.tokens.size(); i++) {
           Vector tv = (Vector) callExp.tokens.elementAt(i);
           for (int j = 0; j < tv.size(); j++) {
             TLAToken tok = (TLAToken) tv.elementAt(j);
             expr.addToken(tok);
           }
         }
       }
       expr.addToken(PcalTranslate.BuiltInToken(")"));
       expr.normalize();
       sass.rhs = expr;
       sass.setOrigin(this.getOrigin());
       // set headAssign
       headAssign.ass.addElement(sass);
       // <tailAssign> = chanName[dim] := Tail(chanName[dim]/@)
       AST.Assign tailAssign = new AST.Assign();
       tailAssign.ass = new Vector();
       tailAssign.line = line ;
       tailAssign.col  = col ;
       tailAssign.setOrigin(this.getOrigin());
       // chanName[dim]
       sass = new AST.SingleAssign();
       sass.line = line;
       sass.col  = col;
       sass.lhs.var = channelName;
       if(callExp.tokens != null) {
         sass.lhs.sub = callExp.cloneAndNormalize();
       } else {
         sass.lhs.sub = new TLAExpr(new Vector());
       }
       // Tail(chanName[dim]/@)
       expr = new TLAExpr();
       expr.addLine();
       String prevChannel = (channel.dimensions.size() == 0) ? channelName : "@";
       expr.addToken(PcalTranslate.BuiltInToken(" Tail(" + prevChannel + ") ")); 
       expr.normalize();
       sass.rhs = expr;
       sass.setOrigin(this.getOrigin());
       // set tailAssign
       tailAssign.ass.addElement(sass);
       // set result
       result.addElement(when);
       result.addElement(headAssign);
       result.addElement(tailAssign);
       
       return result;
     }
     
     public Vector multicast(Channel channel, String channelName, TLAExpr msg) throws ParseAlgorithmException {
       Vector result = new Vector();
       if(! (channelType == CHANNEL_TYPE_UNORDERED
          || channelType == CHANNEL_TYPE_FIFO) ) {
            PcalDebug.ReportBug("Unexpected channel type.");
            return null;
       }

       // For CHANNEL_TYPE_UNORDERED - bag
       // channelName = [ <<v1,v2,...>> \in DOMAIN channelName |->
       //                        IF v1 \in D1, v2 \in D2, ...
       //                           THEN chan[v1,v2,...] (+) [fv \in {message} |-> 1]
       //                           ELSE chan[v1,v2,...]
       // For CHANNEL_TYPE_UNORDERED set
       // channelName = [ <<v1,v2,...>> \in DOMAIN channelName |->
       //                        IF v1 \in D1, v2 \in D2, ...
       //                           THEN chan[v1,v2,...] \cup message
       //                           ELSE chan[v1,v2,...]
       // For CHANNEL_TYPE_FIFO
       // channelName = [ <<v1,v2,...>> \in DOMAIN channelName |->
       //                        IF v1 \in D1, v2 \in D2, ...
       //                           THEN Append(chan[v1,v2,...], message)
       //                           ELSE chan[v1,v2,...]
       AST.SingleAssign sass = new AST.SingleAssign();
       sass.line = line;
       sass.col = col;
       sass.lhs.var = channel.var;
       sass.lhs.sub = new TLAExpr(new Vector<>());

       Vector dimensions = new Vector(); // vector of tokens (the names of the vars for each dimension)
       Vector dimensionTypes = new Vector(); // vector of vectors of tokens
       Vector dt = new Vector(); // buffer to store each dimensionType (which is a vector of tokens) 
       int buildPhase = 0; // 0 = dimensions, 1 = dimensionTypes, 2 = message (after "|->")

       Vector thenExp = new Vector();
       Vector elseExp = new Vector();

       // extract v1,v2,... and D1,D2,...
       // prepare THEN (the message part)
       for(int i = 0; i < msg.tokens.size(); i++) {
         Vector line = (Vector) msg.tokens.elementAt(i);
         for (int j = 0; j < line.size(); j++) {
           TLAToken tok = (TLAToken) line.elementAt(j);
           if(buildPhase == 0) {
             if(tok.type == TLAToken.IDENT) {
               dimensions.add(tok);
               dt = new Vector();
               buildPhase = 1;
             } else if(!tok.string.equals("[")) { // if not the leading "["
               PcalDebug.reportError("Bad format for message in multicast."+tok.string);
             }
           } else {
             if(buildPhase == 1) {
               // get the dimension type
               if(!tok.string.equals(",") && !tok.string.equals("|->")) {
                 dt.add(tok);
               } else {
                 if(tok.string.equals(",")){ // next dimension
                   dimensionTypes.add(dt);
                   buildPhase = 0;
                 } else {
                   if (tok.string.equals("|->")) { // done with dimensions
                     dimensionTypes.add(dt);
                     buildPhase = 2;
                   }
                 }
               }
             } else { // buildPhase == 2, ie the expression we want to multicast
               if ( (i != msg.tokens.size()-1) || (j != line.size()-1) ) { // if not the ending "]"
                 thenExp.add((TLAToken) line.elementAt(j));
               }
             }
           }
         }
       }

       //compare with dimensions within a channel and throw an error if we find a length mismatch
       if(channel.dimensions != null
          && dimensions.size() > 1 // if not using only one variable
          && channel.dimensions.size() != dimensions.size()) { // then the number of variables should be that of the channel
         throw new ParseAlgorithmException("Multicast function expected " + channel.dimensions.size() +" dimensions ");
       }
       
       // build ELSE:  channel[v1,v2,...]
       elseExp.add(PcalTranslate.IdentToken(channelName));
       elseExp.add(PcalTranslate.BuiltInToken("["));
       for(int i = 0; i < dimensions.size(); i++) {
         // use the string instead of the token for the layout
         // (otherwise the positions of the original token impact the position in the layout)
         elseExp.add(PcalTranslate.IdentToken(((TLAToken) dimensions.get(i)).string));
         if(i != dimensions.size() - 1) {
           elseExp.add(PcalTranslate.BuiltInToken(","));
         }
       }
       elseExp.add(PcalTranslate.BuiltInToken("]"));

       TLAExpr expr = new TLAExpr();
       expr.addLine();

       expr.addToken(PcalTranslate.BuiltInToken("["));

       // build <<v1,v2,...>> \in DOMAIN channelName |-> IF
       if(dimensions.size() == 1) { // if only one dimension no need for sequence
         expr.addToken(PcalTranslate.IdentToken(((TLAToken) dimensions.get(0)).string));
       } else {
         expr.addToken(PcalTranslate.BuiltInToken("<<"));
         for(int i = 0; i < dimensions.size(); i++) {
           expr.addToken(PcalTranslate.IdentToken(((TLAToken) dimensions.get(i)).string));
           if(i != dimensions.size() - 1) {
             expr.addToken(PcalTranslate.BuiltInToken(","));
           }
         }
         expr.addToken(PcalTranslate.BuiltInToken(">>"));
       }
			
       expr.addToken(PcalTranslate.BuiltInToken(" \\in DOMAIN "));
       expr.addToken(PcalTranslate.IdentToken(channelName));
       expr.addToken(PcalTranslate.BuiltInToken(" |-> "));
       expr.addToken(PcalTranslate.BuiltInToken(" IF "));
       // build IF body
       // IF v1 \in D1, v2 \in D2, ...
       for(int i = 0; i < dimensions.size(); i++) {
         expr.addToken(PcalTranslate.IdentToken(((TLAToken) dimensions.get(i)).string));
         Vector dti = (Vector) dimensionTypes.get(i);
         for(int j = 0; j < dti.size(); j++) {
           // HC: the space token is just fo the layout, probably can be done more properly in generation
           expr.addToken(PcalTranslate.BuiltInToken(" "));
           expr.addToken(PcalTranslate.IdentToken(((TLAToken) dti.get(j)).string));
         }
         if(i != dimensions.size() - 1) {
           expr.addToken(PcalTranslate.BuiltInToken(" /\\ "));
         }
       }
       expr.addLine();

       // build THEN body 
       // indentation can improved
       expr.addToken(PcalTranslate.BuiltInToken(" THEN "));
       if(channelType == CHANNEL_TYPE_FIFO) {
         expr.addToken(PcalTranslate.BuiltInToken(" Append("));
       }
       expr.addToken(PcalTranslate.IdentToken(channelName));
       expr.addToken(PcalTranslate.BuiltInToken("["));
       for(int i = 0; i < dimensions.size(); i++) {
         expr.addToken(PcalTranslate.IdentToken(((TLAToken) dimensions.get(i)).string));
         if(i != dimensions.size() - 1) {
           expr.addToken(PcalTranslate.BuiltInToken(","));
         }
       }
       expr.addToken(PcalTranslate.BuiltInToken("]"));
       if(channelType == CHANNEL_TYPE_UNORDERED) {
         if(PcalParams.setChannels){
           expr.addToken(PcalTranslate.BuiltInToken(" \\cup "));
           expr.addToken(PcalTranslate.BuiltInToken("{"));
         } else { // bag
           expr.addToken(PcalTranslate.BuiltInToken(" (+) "));
           // expr.addToken(PcalTranslate.BuiltInToken("["));
           // String freshVar = "__v" + varIndex++ + "__";
           // expr.addToken(PcalTranslate.BuiltInToken(freshVar));
           // expr.addToken(PcalTranslate.BuiltInToken(" \\in "));
           // expr.addToken(PcalTranslate.BuiltInToken("{"));
           expr.addToken(PcalTranslate.IdentToken("SetToBag"));
           expr.addToken(PcalTranslate.BuiltInToken("("));
           expr.addToken(PcalTranslate.BuiltInToken("{"));
         }
       } else if(channelType == CHANNEL_TYPE_FIFO) {
         expr.addToken(PcalTranslate.BuiltInToken(", "));
       }
       // insert the message part
       for(int i = 0; i < thenExp.size(); i++) {
         TLAToken tok = (TLAToken) thenExp.elementAt(i);
         tok.column = 0;
         expr.addToken(tok);
       }
       if(channelType == CHANNEL_TYPE_UNORDERED) {
         if(PcalParams.setChannels){
           expr.addToken(PcalTranslate.BuiltInToken("} "));
         } else { // bag
           expr.addToken(PcalTranslate.BuiltInToken("}"));
           // expr.addToken(PcalTranslate.BuiltInToken(" |-> "));
           // expr.addToken(PcalTranslate.BuiltInToken("1"));
           // expr.addToken(PcalTranslate.BuiltInToken("]"));
           expr.addToken(PcalTranslate.BuiltInToken(")"));
         }
       } else if(channelType == CHANNEL_TYPE_FIFO) {
         expr.addToken(PcalTranslate.BuiltInToken(")"));
       }
       expr.addLine();
       expr.addToken(PcalTranslate.BuiltInToken(" ELSE "));
       // insert the ELSE body
       for(int i = 0; i < elseExp.size(); i++) {
         TLAToken tok = (TLAToken) elseExp.elementAt(i);
         expr.addToken(tok);
       }
       expr.addToken(PcalTranslate.BuiltInToken("]"));
       expr.normalize();
       sass.rhs = expr;
       
       sass.setOrigin(this.getOrigin());
       
       AST.Assign assign = new AST.Assign();
       assign.ass = new Vector();
       assign.line = line ;
       assign.col  = col ;
       assign.setOrigin(this.getOrigin());
       
       assign.ass.addElement(sass);
       
       result.addElement(assign);
       return result;
     }

     @Override
     public String toString()
     {
       return
         Indent(lineCol()) +
                    "[chan |-> \"" + var + "\", " +
                    "eqOrIn |-> " + boolToEqOrIn(isEq) + ", " +
                    "val |-> " + val.toString() +  ", " +
                    "dim |-> " + dimensions.toString() + "]" +
         EndIndent() ;
     }
   }

   public static class ChannelSendCall extends AST{
   	public String type = "";
   	public String channelName = null ;
   	public TLAExpr callExp = new TLAExpr(new Vector());
   	public TLAExpr msg = null;
   	
   	public ChannelSendCall() {};
   	public String toString()
   	{ return 
   			Indent(lineCol()) + 
   			"[ChannelSender:" + NewLine() +
   			" type |-> \"" + type + "\"," + NewLine() +
   			Indent(" channel |-> ") + channelName +
   			EndIndent() + NewLine() +
   			Indent(" callExp |-> ") + callExp +
   			EndIndent() + NewLine() +
   			Indent(" msg |-> ") + msg + "]" +
   			EndIndent() ;
   	}
   	
     	/**
     	 * generates the body for a send call
     	 * @param channel
     	 * @return
     	 */
   	public Vector generateBodyTemplate(Channel channel) {
      return channel.send(msg, callExp);
   	}
   	
		/**
		 * @param channel
		 * @return
		 * @throws ParseAlgorithmException 
		 */
		public Vector generateMulticastBodyTemplate(Channel channel) throws ParseAlgorithmException {
   		return channel.multicast(channel, channelName, msg);
		}

   }
  
   public static class ChannelReceiveCall extends AST{
	   public String channelName = "";
	   public TLAExpr callExp = new TLAExpr(new Vector());
	   public Vector args;
	   public String targetVarName = "";
	   public TLAExpr targetExp = new TLAExpr(new Vector());
	   public ChannelReceiveCall() {};
	   public String toString()
	   { return 
			   Indent(lineCol()) + 
			   "[ChannelReceiver:" + NewLine() +
			   Indent(" channel |-> ") + channelName + "," +
			   EndIndent() + NewLine() +
			   Indent(" callExp |-> ") + callExp + "," +
			   EndIndent() + NewLine() +
			   Indent(" targetVar |-> ") + targetVarName + "," +
			   EndIndent() + NewLine() +
			   Indent(" targetExp |-> ") + targetExp + "]" +
			   EndIndent() ;
	   }

	   public Vector generateBodyTemplate(Channel channel, VarDecl targetVar) {
		   return channel.receive(targetVar, callExp, targetExp);
	   }
   }
   
  public static class Thread extends AST{
	  public String    name  = "";
    public int fairness = UNFAIR_PROC ; // unused for the moment
	  public Vector  minusLabels = new Vector();
	  public Vector  plusLabels = new Vector();
	  public Vector  proceduresCalled = new Vector();
	  public TLAExpr   id    = null ;
	  public Vector    body  = null ; // of LabeledStmt
	  public Integer index = null;

	  public Thread() { };
	  public String toString() {
		  return
				  Indent(lineCol()) +
				  "[name   |-> \"" + name + "\"," 
				  + NewLine() +
          " fairness |-> \"" 
          + FairnessString[fairness] + "\", minusLabels |-> "
				  + VectorToSeqQuotedString(minusLabels) + ", plusLabels |->"
				  + VectorToSeqQuotedString(plusLabels) + ", proceduresCalled |->"
				  + VectorToSeqQuotedString(proceduresCalled) + ","
				  + NewLine() +
				  " id     |-> " + id.toString() + "," + NewLine() +
				  Indent(" body   |-> ") + 
				  VectorToSeqString(body) + "]" + ", " + 
				  EndIndent() + 
				  EndIndent();

	  }
  }
  // end For Distributed PlusCal	
    
 }
