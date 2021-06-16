
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
import java.util.ArrayList;
import java.util.List;
import java.util.Vector;

import pcal.exception.ParseAlgorithmException;


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

    //For Distributed PlusCal. Channels	
    public static AST.ChannelSendCall ChannelSenderObj;
    public static AST.ChannelReceiveCall ChannelReceiverObj;
    public static AST.ChannelClearCall ChannelClearObj;
    public static AST.ChannelSendWithClockCall ChannelSendWithClockObj;
    public static AST.ChannelReceiveWithClockCall ChannelReceiveWithClockObj;
    // For Distributed Pluscal. Logical clocks
    public static AST.ClockIncreaseCall ClockIncreaseObj;
    public static AST.ClockUpdateCall ClockUpdateObj;
    public static AST.ClockResetCall ClockResetObj;
    
    public static final String SELF = "slf";
    
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
        // For Distributed Pluscal. Channels
        ChannelSenderObj   =  new AST.ChannelSendCall();
        ChannelReceiverObj =  new AST.ChannelReceiveCall();
        ChannelClearObj   = new AST.ChannelClearCall();
        ChannelSendWithClockObj = new AST.ChannelSendWithClockCall();
        ChannelReceiveWithClockObj = new  AST.ChannelReceiveWithClockCall();
        //For Distributed Pluscal. Logical clocks
        ClockIncreaseObj   = new AST.ClockIncreaseCall();
        ClockUpdateObj     = new AST.ClockUpdateCall();
        ClockResetObj      = new AST.ClockResetCall();
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
        public Vector<Thread> threads = null;

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
                 // Indent(" body   |-> ") + 
                    // VectorToSeqString(body) + "]" +
                Indent(" body   |-> ") + 
                ((body == null) ? "_" :VectorToSeqString(body)) + "]" +  
                // For Distributed PlusCal	
                Indent(",  threads   |-> ") +
                ((threads == null || threads.size() == 0) ? "<<>>" : VectorToSeqString(threads)) + "]" +
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
               // Indent(" body   |-> ") + 
                  // VectorToSeqString(body) + "]" +
              Indent(" body   |-> ") + 
              ((body == null) ? "_" :VectorToSeqString(body)) + "]" +  
              // For Distributed PlusCal	
              Indent(",  threads   |-> ") +
              ((threads == null || threads.size() == 0) ? "<<>>" : VectorToSeqString(threads)) + "]" +
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
   
   
   //classes For Distributed PlusCal
      
   //For Distributed PlusCal	
   public static abstract class Channel extends VarDecl{

   	public Channel() {};
   	List dimensions = null;
   	public abstract Vector send(Channel channel, String channelName, TLAExpr msg, TLAExpr callExp);
   	public abstract Vector receive(Channel channel, String channelName, VarDecl targetVar, TLAExpr callExp, TLAExpr targetExp);
   	// For Distributed PLuscal. Add TLAExpr msg argument to implement new broadcast
   	public abstract Vector broadcast(Channel channel, String channelName, TLAExpr msg, TLAExpr callExp) throws ParseAlgorithmException;
   	public abstract Vector multicast(Channel channel, String channelName, TLAExpr msg) throws ParseAlgorithmException;
   	// For Distributed Pluscal. Add String channelName and TLAExpr callExp arguments to allow new clear functionality
   	public abstract Vector clear(Channel channel, String channelName, TLAExpr callExp) throws ParseAlgorithmException;
   	
   	// For Distributed PlusCal. Channel operations with logical clocks
   	public abstract Vector sendWithClock(Channel channel, String channelName, TLAExpr msg, TLAExpr callExp, TLAExpr clock);
   	public abstract Vector receiveWithClock(Channel channel, String channelName, VarDecl targetVar, TLAExpr callExp, TLAExpr targetExp, TLAExpr clock);
   	public abstract Vector broadcastWithClock(Channel channel, String channelName, TLAExpr msg, TLAExpr callExp, TLAExpr clock) throws ParseAlgorithmException;
   }
   
   public static class UnorderedChannel extends Channel{

   	public UnorderedChannel() {};
   	
   	@Override
   	public Vector send(Channel channel, String channelName, TLAExpr msg, TLAExpr callExp) {
   		Vector result = new Vector();

   		AST.SingleAssign sass = new AST.SingleAssign();
   		sass.line = line;
   		sass.col  = col;
   		sass.lhs.var = channel.var;

   		TLAExpr expr = new TLAExpr();

   		if(callExp.tokens != null) {
   			sass.lhs.sub = callExp;
   		}else {
   			sass.lhs.sub = new TLAExpr(new Vector());
   		}

   		expr = new TLAExpr();
   		expr.addLine();
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

   		expr.addToken(PcalTranslate.BuiltInToken(" \\cup "));
   		expr.addToken(PcalTranslate.BuiltInToken("{"));

   		for(int i = 0; i < msg.tokens.size(); i++) {

   			Vector tv = (Vector) msg.tokens.elementAt(i);
   			for (int j = 0; j < tv.size(); j++) {
   				TLAToken tok = (TLAToken) tv.elementAt(j);

   				expr.addToken(tok);
   			}
   		}

   		expr.addToken(PcalTranslate.BuiltInToken("}"));
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
		public Vector receive(Channel channel, String channelName, VarDecl targetVar, TLAExpr callExp, TLAExpr targetExp) {

			Vector result = new Vector();
			// For Distributed PlusCal. append _ to overcome variable name clash
			String tempVarName = "_" + channelName.toLowerCase().charAt(0) + line + col;

			TLAExpr exp = new TLAExpr();

			AST.With with = new AST.With();
			with.col = line;
			with.line = col;
			with.var = tempVarName;
			with.isEq = false;

			exp = new TLAExpr();
			exp.addLine();

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
			
			with.exp = exp;
			with.setOrigin(this.getOrigin());

			Vector doBody = new Vector();

			AST.SingleAssign sass = new AST.SingleAssign();
			sass.line = line;
			sass.col  = col;
			sass.lhs.var = targetVar.var;
			
			TLAExpr expr = new TLAExpr();

			if(targetExp.tokens != null) {
				for(int i = 0; i < targetExp.tokens.size(); i++) {

					Vector tv = (Vector) targetExp.tokens.elementAt(i);
					for (int j = 0; j < tv.size(); j++) {
						TLAToken tok = (TLAToken) tv.elementAt(j);
						expr.addToken(tok);
					}
				}
				sass.lhs.sub = expr;
			} else {
				sass.lhs.sub = new TLAExpr(new Vector());
			}

			
			expr = new TLAExpr();
			expr.addLine();
			expr.addToken(PcalTranslate.IdentToken(tempVarName));

			sass.rhs = expr;
			sass.setOrigin(this.getOrigin());

			AST.Assign assign = new AST.Assign();
			assign.ass = new Vector();
			assign.line = line ;
			assign.col  = col ;
			assign.setOrigin(this.getOrigin());

			assign.ass.addElement(sass);


			sass = new AST.SingleAssign();
			sass.line = line;
			sass.col  = col;
			sass.lhs.var = channel.var;

			expr = new TLAExpr();
			expr.addLine();
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
			
			expr.addToken(PcalTranslate.BuiltInToken(" \\ "));
			expr.addToken(PcalTranslate.BuiltInToken("{"));
			expr.addToken(PcalTranslate.IdentToken(tempVarName));
			expr.addToken(PcalTranslate.BuiltInToken("}"));

			sass.rhs = expr;

			if(callExp.tokens != null) {
				sass.lhs.sub = callExp;
			}else {
				sass.lhs.sub = new TLAExpr(new Vector());
			}

			sass.setOrigin(this.getOrigin());
			assign.ass.addElement(sass);
			doBody.addElement(assign);
			with.Do = doBody;
			result.addElement(with);

			return result;
		}

		@Override
		public Vector broadcast(Channel channel, String channelName, TLAExpr msg, TLAExpr callExp) throws ParseAlgorithmException {
			
			int chan_dim = (channel.dimensions == null) ? 0 : channel.dimensions.size();    
			int callExp_dim =  PcalTLAGen.getCallExprValues(callExp).size();
			// compare channel dimension with call expr. incase of mismatch throw exception
			if ( chan_dim < callExp_dim ) {
				throw new ParseAlgorithmException("channel dimension is less than call Expression dimension. ");
			}
			
			if (chan_dim == callExp_dim ) {
				return send(channel, channelName, msg, callExp);
			}
			
			Vector result = new Vector();
			AST.SingleAssign sass = new AST.SingleAssign();
			sass.line = line;
			sass.col  = col;
			sass.lhs.var = channel.var;

			sass.lhs.sub = new TLAExpr(new Vector());
			
			sass.setOrigin(this.getOrigin());
			
			TLAExpr expr = new TLAExpr();
			expr.addLine();    			
			
			ArrayList<String> temp_vars = new ArrayList<>();
			
			// n0 \in Nodes --- builds this part
			for(int i = 0; i < channel.dimensions.size(); i++) {
				String dimension = (String) channel.dimensions.get(i);
				String tempVarName = "_" + dimension.toLowerCase().charAt(0) + i;
				temp_vars.add(tempVarName);
				if(i == 0) {
					expr.addToken(PcalTranslate.BuiltInToken("["));
				}
				expr.addToken(PcalTranslate.IdentToken(tempVarName));
				expr.addToken(PcalTranslate.BuiltInToken(" \\in "));
				expr.addToken(PcalTranslate.IdentToken(dimension));


				if(channel.dimensions.size() != 1 && i != channel.dimensions.size() - 1) {
					expr.addToken(PcalTranslate.BuiltInToken(", "));
				}
			}
			
			expr.addToken(PcalTranslate.BuiltInToken(" |-> "));
			
			if (callExp_dim == 1) {
				expr.addToken(PcalTranslate.BuiltInToken("IF"));
				expr.addToken(PcalTranslate.BuiltInToken(" _n0 = " + callExp.toPlainString().substring(1, callExp.toPlainString().length()-1)));
				expr.addToken(PcalTranslate.BuiltInToken(" THEN "));
				expr.addToken(PcalTranslate.BuiltInToken(channelName + "[_n0, _n1] \\cup "));
				
				expr.addToken(PcalTranslate.BuiltInToken("{"));
				for(int i = 0; i < msg.tokens.size(); i++) {

		   			Vector tv = (Vector) msg.tokens.elementAt(i);
		   			for (int j = 0; j < tv.size(); j++) {
		   				TLAToken tok = (TLAToken) tv.elementAt(j);

		   				expr.addToken(tok);
		   			}
		   		}
				expr.addToken(PcalTranslate.BuiltInToken("}"));
				
				expr.addToken(PcalTranslate.BuiltInToken(" ELSE "));
				expr.addToken(PcalTranslate.BuiltInToken(channelName + "[_n0, _n1]"));
				
			} 
			else {			
				expr.addToken(PcalTranslate.BuiltInToken(channelName));
				expr.addToken(PcalTranslate.BuiltInToken("["));
				for(int i = 0; i < channel.dimensions.size(); i++) {
					expr.addToken(PcalTranslate.IdentToken(temp_vars.get(i)));
					if(channel.dimensions.size() != 1 && i != channel.dimensions.size() - 1) {
						expr.addToken(PcalTranslate.BuiltInToken(", "));
					}
				}
				expr.addToken(PcalTranslate.BuiltInToken("]"));		
		
				expr.addToken(PcalTranslate.BuiltInToken(" \\cup "));			
		   		expr.addToken(PcalTranslate.BuiltInToken("{"));
		   		
		   		for(int i = 0; i < msg.tokens.size(); i++) {
		
		   			Vector tv = (Vector) msg.tokens.elementAt(i);
		   			for (int j = 0; j < tv.size(); j++) {
		   				TLAToken tok = (TLAToken) tv.elementAt(j);
		
		   				expr.addToken(tok);
		   			}
		   		}
		   		expr.addToken(PcalTranslate.BuiltInToken("}"));
			}
			
			expr.addToken(PcalTranslate.BuiltInToken("]"));
			expr.setOrigin(this.getOrigin());
			expr.normalize();

			sass.rhs = expr;

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
		public Vector multicast(Channel channel, String channelName, TLAExpr msg) throws ParseAlgorithmException {

			Vector result = new Vector();

			AST.SingleAssign sass = new AST.SingleAssign();
			sass.line = line;
			sass.col  = col;
			sass.lhs.var = channel.var;

			sass.lhs.sub = new TLAExpr(new Vector<>());
			
			TLAExpr expr = new TLAExpr();


			List dimensions = new ArrayList<>(); 
			List dimensionTypes = new ArrayList<>(); 

			TLAExpr thenExp = new TLAExpr();
			thenExp.addLine();

			TLAExpr elseExp = new TLAExpr();
			elseExp.addLine();

			for(int i = 0; i < msg.tokens.size(); i++) {

				Vector tv = (Vector) msg.tokens.elementAt(i);

				for (int j = 0; j < tv.size(); j++) {
					TLAToken tok = (TLAToken) tv.elementAt(j);

					if(tok.type == TLAToken.IDENT) {
						
						if(tok.string.equals("self")) {
							dimensions.add(SELF);
							//add to types just to maintain order between the 2 lists
							dimensionTypes.add(SELF);

						} else {
							dimensions.add(tok.string);

							StringBuffer sb = new StringBuffer();
							
							//get the rest of the expression
							tok = (TLAToken) tv.elementAt(++j);
							while(!tok.string.equals(",") && !tok.string.equals("|->")) {
								sb.append(" " + tok.string);
								tok = (TLAToken) tv.elementAt(++j);
							}
							dimensionTypes.add(sb.toString());
						}
					}

					if(tok.string.equals("|->")) {
						//everything after |-> is the expression we want to multicast
						tok = (TLAToken) tv.elementAt(++j);

						//while the next char is , -1 to excluse ] at the end
						while(j < tv.size() - 1) {
							thenExp.addToken((TLAToken) tv.elementAt(j));
							j++;
						}
						break;
					}
				}
			}

			//compare with dimensions within a channel and throw an error if we find a length mismatch
			if(channel.dimensions != null && channel.dimensions.size() != dimensions.size()) {
				throw new ParseAlgorithmException("multicast function expected " + channel.dimensions.size() +" dimentions ");
			}
			
			elseExp.addToken(PcalTranslate.IdentToken(channelName));
			elseExp.addToken(PcalTranslate.IdentToken(dimensions.toString()));

			expr = new TLAExpr();
			expr.addLine();

			expr.addToken(PcalTranslate.BuiltInToken("["));

			//get identifier used in the expression with \cup message
			if(dimensions.size() == 1) {
				expr.addToken(PcalTranslate.IdentToken(dimensions.toString().substring(1, dimensions.toString().length()-1)));
			} else {
				expr.addToken(PcalTranslate.BuiltInToken("<<"));
				expr.addToken(PcalTranslate.IdentToken(dimensions.toString().substring(1, dimensions.toString().length()-1)));
				expr.addToken(PcalTranslate.BuiltInToken(">>"));
			}
			
			expr.addToken(PcalTranslate.BuiltInToken(" \\in DOMAIN "));
			expr.addToken(PcalTranslate.IdentToken(channelName));
			expr.addToken(PcalTranslate.BuiltInToken(" |-> "));
			expr.addToken(PcalTranslate.BuiltInToken(" IF "));

			for(int i = 0; i < dimensions.size(); i++) {

				if(dimensions.get(i).equals(SELF)) {
					expr.addToken(PcalTranslate.IdentToken(SELF));
					expr.addToken(PcalTranslate.BuiltInToken(" = self "));
				} else {
					expr.addToken(PcalTranslate.IdentToken(dimensions.get(i).toString()));
					expr.addToken(PcalTranslate.IdentToken(dimensionTypes.get(i).toString()));
				}
				
				if(i != dimensions.size() -1) {
					//fix indentation here, use a stringbuffer and spaceout 
					expr.addLine();
					expr.addToken(PcalTranslate.BuiltInToken(" /\\ "));
				}
			}

			expr.addToken(PcalTranslate.BuiltInToken(" THEN "));

			expr.addToken(PcalTranslate.IdentToken(channelName));
			expr.addToken(PcalTranslate.IdentToken(dimensions.toString()));

			expr.addToken(PcalTranslate.BuiltInToken(" \\cup "));
			expr.addToken(PcalTranslate.BuiltInToken(" {"));
			

			for(int i = 0; i < thenExp.tokens.size(); i++) {

				Vector tv = (Vector) thenExp.tokens.elementAt(i);
				for (int j = 0; j < tv.size(); j++) {
					TLAToken tok = (TLAToken) tv.elementAt(j);
					tok.column = 0;
					expr.addToken(tok);
				}
			}
			
			expr.addToken(PcalTranslate.BuiltInToken("} "));

			expr.addToken(PcalTranslate.BuiltInToken(" ELSE "));

			for(int i = 0; i < elseExp.tokens.size(); i++) {

				Vector tv = (Vector) elseExp.tokens.elementAt(i);
				for (int j = 0; j < tv.size(); j++) {
					TLAToken tok = (TLAToken) tv.elementAt(j);
					expr.addToken(tok);
				}
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
		public Vector clear(Channel channel, String channelName, TLAExpr callExp) throws ParseAlgorithmException {
			Vector result = new Vector();
			
			// For Distributed PLuscal. 
			int chan_dim = (channel.dimensions == null) ? 0 : channel.dimensions.size();
			int callExp_dim = PcalTLAGen.getCallExprValues(callExp).size();
			
			// compare channel dimension with call expr. incase of mismatch throw exception
			if ( chan_dim < callExp_dim ) {
				throw new ParseAlgorithmException("channel dimension is less than call Expression dimension. ");
			}
			
			AST.SingleAssign sass = new AST.SingleAssign();
			sass.line = line;
			sass.col  = col;
			sass.lhs.var = channel.var;
			TLAExpr expr;
			
			if (chan_dim == callExp_dim) { // when chan and clear(chan)| chan[N] and clear(chan[self]| chan[N, N] and clear(chan[self, self])
				if(callExp.tokens != null)
		   			sass.lhs.sub = callExp;
		   		else
		   			sass.lhs.sub = new TLAExpr(new Vector());
		   		
				sass.setOrigin(this.getOrigin());

				expr = new TLAExpr();
				expr.addLine();
				
				expr.addToken(PcalTranslate.BuiltInToken("{"));
				expr.addToken(PcalTranslate.BuiltInToken("}"));
			}
			else if ( chan_dim != 0 && callExp_dim == 0 ) { // when chan[N] or chan[N,N] and we say clear(chan);
				sass.lhs.sub = new TLAExpr(new Vector());
				sass.setOrigin(this.getOrigin());

				expr = new TLAExpr();
				expr.addLine();
				
				for(int i = 0; i < channel.dimensions.size(); i++) {
					String dimension = (String) channel.dimensions.get(i);
					// For Distributed PlusCal. append _ to overcome variable name clash
					String tempVarName = String.valueOf("_" + dimension.toLowerCase().charAt(0)) + i;
					
					if(i == 0) {
						expr.addToken(PcalTranslate.BuiltInToken("["));
					}
					expr.addToken(PcalTranslate.IdentToken(tempVarName));
	
					if(channel.dimensions.size() != 1 && i != channel.dimensions.size() - 1) {
						expr.addToken(PcalTranslate.BuiltInToken(", "));
					}
				}
	
				expr.addToken(PcalTranslate.BuiltInToken(" \\in "));
				expr.addToken(PcalTranslate.IdentToken(channel.dimensions.get(0).toString()));
				expr.addToken(PcalTranslate.BuiltInToken(" |-> "));

				expr.addToken(PcalTranslate.BuiltInToken("{"));
				expr.addToken(PcalTranslate.BuiltInToken("}"));

				expr.addToken(PcalTranslate.BuiltInToken("]"));
			}
			else { // when chan[N, N] and clear(chan[self])
				sass.lhs.sub = new TLAExpr(new Vector());
				sass.setOrigin(this.getOrigin());

				expr = new TLAExpr();
				expr.addLine();
				
				for(int i = 0; i < channel.dimensions.size(); i++) {
					String dimension = (String) channel.dimensions.get(i);
					// For Distributed PlusCal. append _ to overcome variable name clash
					String tempVarName = "_" + dimension.toLowerCase().charAt(0) + i;
					
					if(i == 0) {
						expr.addToken(PcalTranslate.BuiltInToken("["));
					}
					expr.addToken(PcalTranslate.IdentToken(tempVarName));
	
					if(channel.dimensions.size() != 1 && i != channel.dimensions.size() - 1) {
						expr.addToken(PcalTranslate.BuiltInToken(", "));
					}
				}
				
				expr.addToken(PcalTranslate.BuiltInToken(" \\in "));
				expr.addToken(PcalTranslate.IdentToken(channel.dimensions.get(0).toString()));
				expr.addToken(PcalTranslate.BuiltInToken(" |->"));
				expr.addToken(PcalTranslate.BuiltInToken(" IF "));
				expr.addToken(PcalTranslate.BuiltInToken("_n0 = " + callExp.toPlainString().substring(1, callExp.toPlainString().length()-1)));
				expr.addToken(PcalTranslate.BuiltInToken(" THEN {}"));
				expr.addToken(PcalTranslate.BuiltInToken(" ELSE "));
				expr.addToken(PcalTranslate.BuiltInToken(channelName + "[_n0, _n1]"));
				expr.addToken(PcalTranslate.BuiltInToken("]"));
			}
			
			expr.setOrigin(this.getOrigin());
			expr.normalize();

			sass.rhs = expr;

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
		public Vector sendWithClock(Channel channel, String channelName, TLAExpr msg, TLAExpr callExp, TLAExpr clock) {
			Vector result = new Vector();
			
	   		AST.SingleAssign sass = new AST.SingleAssign();
	   		sass.line = line;
	   		sass.col  = col;
	   		sass.lhs.var = channel.var;

	   		TLAExpr expr = new TLAExpr();

	   		if(callExp.tokens != null) {
	   			sass.lhs.sub = callExp;
	   		}else {
	   			sass.lhs.sub = new TLAExpr(new Vector());
	   		}

	   		expr = new TLAExpr();
	   		expr.addLine();
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

	   		expr.addToken(PcalTranslate.BuiltInToken(" \\cup "));
	   		expr.addToken(PcalTranslate.BuiltInToken("{"));
	   		expr.addToken(PcalTranslate.BuiltInToken("[msg |-> "));
	   		
	   		for(int i = 0; i < msg.tokens.size(); i++) {

	   			Vector tv = (Vector) msg.tokens.elementAt(i);
	   			for (int j = 0; j < tv.size(); j++) {
	   				TLAToken tok = (TLAToken) tv.elementAt(j);

	   				expr.addToken(tok);
	   			}
	   		}
	   		
	   		expr.addToken(PcalTranslate.BuiltInToken(", "));
	   		expr.addToken(PcalTranslate.BuiltInToken("clock |-> "));
	   		expr.addToken(PcalTranslate.BuiltInToken(clock.toPlainString()));
	   		//expr.addToken(PcalTranslate.BuiltInToken(clock.toPlainString() + " + 1"));
	   		expr.addToken(PcalTranslate.BuiltInToken("]"));
	   		expr.addToken(PcalTranslate.BuiltInToken("}"));
	   		sass.rhs = expr;
	   		
	   		sass.setOrigin(this.getOrigin());

	   		AST.Assign assign = new AST.Assign();
	   		assign.ass = new Vector();
	   		assign.line = line ;
	   		assign.col  = col ;
	   		assign.setOrigin(this.getOrigin());
	   		
	   		assign.ass.addElement(sass);

	   		result.addElement(assign);
	   		
	   		///////////////////////////////
	   		sass = new AST.SingleAssign();
	   		sass.line = line;
	   		sass.col  = col;
	   		sass.lhs.var = clock.toPlainString();

	   		expr = new TLAExpr();

	   		//if(callExp.tokens != null)
	   			//sass.lhs.sub = callExp;
	   		//else
	   			sass.lhs.sub = new TLAExpr(new Vector());
	   		
	   		expr = new TLAExpr();
	   		expr.addLine();
	   		expr.addToken(PcalTranslate.IdentToken(clock.toPlainString()));
	   		
	   		/*
	   		if(callExp.tokens != null) {
	   			for(int i = 0; i < callExp.tokens.size(); i++) {

	   				Vector tv = (Vector) callExp.tokens.elementAt(i);
	   				for (int j = 0; j < tv.size(); j++) {
	   					TLAToken tok = (TLAToken) tv.elementAt(j);

	   					expr.addToken(tok);
	   				}
	   			}
	   		}
	   		*/
	   		
	   		expr.addToken(PcalTranslate.BuiltInToken(" + 1 "));
	   		
	   		sass.rhs = expr;

	   		sass.setOrigin(this.getOrigin());

	   		assign = new AST.Assign();
	   		assign.ass = new Vector();
	   		assign.line = line ;
	   		assign.col  = col ;
	   		assign.setOrigin(this.getOrigin());
	   		
	   		assign.ass.addElement(sass);

	   		result.addElement(assign);
	   		
	   		return result;
		}

		@Override
		public Vector receiveWithClock(Channel channel, String channelName, VarDecl targetVar, TLAExpr callExp,
				TLAExpr targetExp, TLAExpr clock) {
			Vector result = new Vector();
			// For Distributed PlusCal. append _ to overcome variable name clash
			String tempVarName = String.valueOf("_" + channelName.toLowerCase().charAt(0)) + line + col;

			TLAExpr exp = new TLAExpr();

			AST.With with = new AST.With();
			with.col = line;
			with.line = col;
			with.var = tempVarName;
			with.isEq = false;

			exp = new TLAExpr();
			exp.addLine();

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
			
			with.exp = exp;
			with.setOrigin(this.getOrigin());

			Vector doBody = new Vector();

			AST.SingleAssign sass = new AST.SingleAssign();
			sass.line = line;
			sass.col  = col;
			sass.lhs.var = targetVar.var;
			
			TLAExpr expr = new TLAExpr();

			if(targetExp.tokens != null) {
				for(int i = 0; i < targetExp.tokens.size(); i++) {

					Vector tv = (Vector) targetExp.tokens.elementAt(i);
					for (int j = 0; j < tv.size(); j++) {
						TLAToken tok = (TLAToken) tv.elementAt(j);
						expr.addToken(tok);
					}
				}
				sass.lhs.sub = expr;
			} else {
				sass.lhs.sub = new TLAExpr(new Vector());
			}
			
			expr = new TLAExpr();
			expr.addLine();
			
			expr.addToken(PcalTranslate.IdentToken(tempVarName));
			
			sass.rhs = expr;
			sass.setOrigin(this.getOrigin());

			AST.Assign assign = new AST.Assign();
			assign.ass = new Vector();
			assign.line = line ;
			assign.col  = col ;
			assign.setOrigin(this.getOrigin());

			assign.ass.addElement(sass);


			sass = new AST.SingleAssign();
			sass.line = line;
			sass.col  = col;
			sass.lhs.var = channel.var;

			expr = new TLAExpr();
			expr.addLine();
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
			
			expr.addToken(PcalTranslate.BuiltInToken(" \\ "));
			expr.addToken(PcalTranslate.BuiltInToken("{"));
			expr.addToken(PcalTranslate.IdentToken(tempVarName));
			expr.addToken(PcalTranslate.BuiltInToken("}"));
			
			sass.rhs = expr;
			
			if(callExp.tokens != null) {
				sass.lhs.sub = callExp;
			}else {
				sass.lhs.sub = new TLAExpr(new Vector());
			}
			
			sass.setOrigin(this.getOrigin());
			assign.ass.addElement(sass);
			
			///////////
			sass = new AST.SingleAssign();
			sass.line = line;
			sass.col  = col;
			sass.lhs.var = clock.toPlainString();
			
			//if(callExp.tokens != null)
				//sass.lhs.sub = callExp;
			//else
				sass.lhs.sub = new TLAExpr(new Vector());
			
			expr = new TLAExpr();
			expr.addLine();
			
			expr.addToken(PcalTranslate.IdentToken("Max("));
			expr.addToken(PcalTranslate.IdentToken(clock.toPlainString()));
			expr.addToken(PcalTranslate.IdentToken(", "));
			String t = tempVarName + ".clock";
			expr.addToken(PcalTranslate.IdentToken(t));
			expr.addToken(PcalTranslate.IdentToken(") + 1"));
			
			sass.rhs = expr;
			sass.setOrigin(this.getOrigin());
			assign.ass.addElement(sass);
			/////////////////////////////
			
			doBody.addElement(assign);
			with.Do = doBody;
			
			result.addElement(with);
			
			return result;
		}

		@Override
		public Vector broadcastWithClock(Channel channel, String channelName, TLAExpr msg, TLAExpr callExp,
				TLAExpr clock) throws ParseAlgorithmException {
			
			int chan_dim = (channel.dimensions == null) ? 0 : channel.dimensions.size();    
			int callExp_dim =  PcalTLAGen.getCallExprValues(callExp).size();
			// compare channel dimension with call expr. incase of mismatch throw exception
			PcalDebug.reportInfo("chan_dim : " + chan_dim + "     callExp_dim: " + callExp_dim);
			if ( chan_dim < callExp_dim ) {
				throw new ParseAlgorithmException("channel dimension is less than call Expression dimension. ");
			}
			
			if (chan_dim == callExp_dim ) {
				return send(channel, channelName, msg, callExp);
			}
			
			Vector result = new Vector();
			AST.SingleAssign sass = new AST.SingleAssign();
			sass.line = line;
			sass.col  = col;
			sass.lhs.var = channel.var;

			sass.lhs.sub = new TLAExpr(new Vector());
			
			sass.setOrigin(this.getOrigin());
			
			TLAExpr expr = new TLAExpr();
			expr.addLine();    			
			
			ArrayList<String> temp_vars = new ArrayList<>();
			
			// n0 \in Nodes --- builds this part
			for(int i = 0; i < channel.dimensions.size(); i++) {
				String dimension = (String) channel.dimensions.get(i);
				String tempVarName = "_" + dimension.toLowerCase().charAt(0) + i;
				temp_vars.add(tempVarName);
				if(i == 0) {
					expr.addToken(PcalTranslate.BuiltInToken("["));
				}
				expr.addToken(PcalTranslate.IdentToken(tempVarName));
				expr.addToken(PcalTranslate.BuiltInToken(" \\in "));
				expr.addToken(PcalTranslate.IdentToken(dimension));


				if(channel.dimensions.size() != 1 && i != channel.dimensions.size() - 1) {
					expr.addToken(PcalTranslate.BuiltInToken(", "));
				}
			}
			
			expr.addToken(PcalTranslate.BuiltInToken(" |-> "));
			
			if (callExp_dim == 1) {
				expr.addToken(PcalTranslate.BuiltInToken("IF"));
				expr.addToken(PcalTranslate.BuiltInToken(" _n0 = " + callExp.toPlainString().substring(1, callExp.toPlainString().length()-1)));
				expr.addToken(PcalTranslate.BuiltInToken(" THEN "));
				expr.addToken(PcalTranslate.BuiltInToken(channelName + "[_n0, _n1] \\cup "));
				
				expr.addToken(PcalTranslate.BuiltInToken("{"));
				expr.addToken(PcalTranslate.BuiltInToken("[msg |-> "));
				
				for(int i = 0; i < msg.tokens.size(); i++) {

		   			Vector tv = (Vector) msg.tokens.elementAt(i);
		   			for (int j = 0; j < tv.size(); j++) {
		   				TLAToken tok = (TLAToken) tv.elementAt(j);

		   				expr.addToken(tok);
		   			}
		   		}
				
				expr.addToken(PcalTranslate.BuiltInToken(", clock |-> "));
				expr.addToken(PcalTranslate.BuiltInToken(clock.toPlainString()));
		   		expr.addToken(PcalTranslate.BuiltInToken("]"));
				expr.addToken(PcalTranslate.BuiltInToken("}"));
				
				expr.addToken(PcalTranslate.BuiltInToken(" ELSE "));
				expr.addToken(PcalTranslate.BuiltInToken(channelName + "[_n0, _n1]"));
				
			} 
			else {			
				expr.addToken(PcalTranslate.BuiltInToken(channelName));
				expr.addToken(PcalTranslate.BuiltInToken("["));
				for(int i = 0; i < channel.dimensions.size(); i++) {
					expr.addToken(PcalTranslate.IdentToken(temp_vars.get(i)));
					if(channel.dimensions.size() != 1 && i != channel.dimensions.size() - 1) {
						expr.addToken(PcalTranslate.BuiltInToken(", "));
					}
				}
				expr.addToken(PcalTranslate.BuiltInToken("]"));		
		
				expr.addToken(PcalTranslate.BuiltInToken(" \\cup "));			
		   		expr.addToken(PcalTranslate.BuiltInToken("{"));
		   		expr.addToken(PcalTranslate.BuiltInToken("[msg |-> "));
		   		
		   		for(int i = 0; i < msg.tokens.size(); i++) {
		
		   			Vector tv = (Vector) msg.tokens.elementAt(i);
		   			for (int j = 0; j < tv.size(); j++) {
		   				TLAToken tok = (TLAToken) tv.elementAt(j);
		
		   				expr.addToken(tok);
		   			}
		   		}
		   		
		   		expr.addToken(PcalTranslate.BuiltInToken(", clock |-> "));
		   		expr.addToken(PcalTranslate.BuiltInToken(clock.toPlainString()));
		   		expr.addToken(PcalTranslate.BuiltInToken("]"));
		   		expr.addToken(PcalTranslate.BuiltInToken("}"));
			}
			
			expr.addToken(PcalTranslate.BuiltInToken("]"));
			expr.setOrigin(this.getOrigin());
			expr.normalize();

			sass.rhs = expr;

			AST.Assign assign = new AST.Assign();
			assign.ass = new Vector();
			assign.line = line ;
			assign.col  = col ;
			assign.setOrigin(this.getOrigin());

			assign.ass.addElement(sass);

			result.addElement(assign);
			
			///////////////////////////////
			sass = new AST.SingleAssign();
			sass.line = line;
			sass.col  = col;
			sass.lhs.var = clock.toPlainString();
			
			expr = new TLAExpr();
			
			//if(callExp.tokens != null)
				//sass.lhs.sub = callExp;
			//else
				sass.lhs.sub = new TLAExpr(new Vector());
			
			expr = new TLAExpr();
			expr.addLine();
			expr.addToken(PcalTranslate.IdentToken(clock.toPlainString()));
			
			/*
			if(callExp.tokens != null) {
				for(int i = 0; i < callExp.tokens.size(); i++) {
			
					Vector tv = (Vector) callExp.tokens.elementAt(i);
					for (int j = 0; j < tv.size(); j++) {
						TLAToken tok = (TLAToken) tv.elementAt(j);
			
						expr.addToken(tok);
					}
				}
			}
			*/
			
			expr.addToken(PcalTranslate.BuiltInToken(" + 1 "));
			
			sass.rhs = expr;
			
			sass.setOrigin(this.getOrigin());
			
			assign = new AST.Assign();
			assign.ass = new Vector();
			assign.line = line ;
			assign.col  = col ;
			assign.setOrigin(this.getOrigin());
			
			assign.ass.addElement(sass);
			
			result.addElement(assign);
			
			return result;
		}
   	
   }
   
   public static class FIFOChannel extends Channel{
   	public FIFOChannel() {};
   	
		@Override
		public Vector send(Channel channel, String channelName, TLAExpr msg, TLAExpr callExp) {

   		Vector result = new Vector();
   		
			AST.SingleAssign sass = new AST.SingleAssign();
			sass.line = line;
			sass.col  = col;
			sass.lhs.var = channel.var;

			TLAExpr expr = new TLAExpr();
			
			if(callExp.tokens != null) {
				sass.lhs.sub = callExp;
			}else {
				sass.lhs.sub = new TLAExpr(new Vector());
			}
			
			expr.addLine();
			// dostonbek. Append channel name fix.
			if (! (channel.dimensions == null)) {
				expr.addToken(PcalTranslate.BuiltInToken(" Append(@, "));
			}	else {
				expr.addToken(PcalTranslate.BuiltInToken(" Append(" + channelName + ", "));
			}

			for(int i = 0; i < msg.tokens.size(); i++) {
				
				Vector tv = (Vector) msg.tokens.elementAt(i);
				for (int j = 0; j < tv.size(); j++) {
					TLAToken tok = (TLAToken) tv.elementAt(j);

					expr.addToken(tok);
				}
			}
			
			expr.addToken(PcalTranslate.BuiltInToken(")"));
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
		public Vector receive(Channel channel, String channelName,  VarDecl targetVar, TLAExpr callExp, TLAExpr targetExp) {

			Vector result = new Vector();
			// For Distributed PlusCal. append _ to overcome variable name clash
			String tempVarName = "_" + channelName.toLowerCase().charAt(0) + line + col;

			TLAExpr exp = new TLAExpr();

			AST.When when = new AST.When();
			when.col = line;
			when.line = col;

			exp = new TLAExpr();
			exp.addLine();

			exp.addToken(PcalTranslate.BuiltInToken("Len("));
			exp.addToken(PcalTranslate.IdentToken(channel.var));
			
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

			when.exp = exp;
			when.setOrigin(this.getOrigin());

			AST.Assign headAssign = new AST.Assign();
			headAssign.ass = new Vector();
			headAssign.line = line ;
			headAssign.col  = col ;
			headAssign.setOrigin(this.getOrigin());
			
			AST.SingleAssign sass = new AST.SingleAssign();
			sass.line = line;
			sass.col  = col;
			sass.lhs.var = targetVar.var;

			TLAExpr expr = new TLAExpr();
      // HC: fix bug FIFO (06/04/21)
			// expr.addLine(); 
			if(targetExp.tokens != null) {
				for(int i = 0; i < targetExp.tokens.size(); i++) {

					Vector tv = (Vector) targetExp.tokens.elementAt(i);
					for (int j = 0; j < tv.size(); j++) {
						TLAToken tok = (TLAToken) tv.elementAt(j);
						expr.addToken(tok);
					}
				}
				sass.lhs.sub = expr;
			} else {
				sass.lhs.sub = new TLAExpr(new Vector());
			}
			
			expr = new TLAExpr();
			expr.addLine();
			expr.addToken(PcalTranslate.BuiltInToken("Head("));
			expr.addToken(PcalTranslate.IdentToken(channel.var));
			
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

			sass.rhs = expr;
			sass.setOrigin(this.getOrigin());

			headAssign.ass.addElement(sass);

			AST.Assign tailAssign = new AST.Assign();
			tailAssign.ass = new Vector();
			tailAssign.line = line ;
			tailAssign.col  = col ;
			tailAssign.setOrigin(this.getOrigin());
			
			sass = new AST.SingleAssign();
			sass.line = line;
			sass.col  = col;
			sass.lhs.var = channel.var;

			if(callExp.tokens != null) {
				sass.lhs.sub = callExp;
			} else {
				sass.lhs.sub = new TLAExpr(new Vector());
			}
			
			expr = new TLAExpr();
			expr.addLine();
			// dostonbek. Receive channel name fix.
			if ( callExp.tokens.size() == 0) {
				expr.addToken(PcalTranslate.BuiltInToken(" Tail(" + channelName + ")"));
			} else {
				expr.addToken(PcalTranslate.BuiltInToken(" Tail(@) "));
			}
			
			sass.rhs = expr;

			sass.setOrigin(this.getOrigin());
			tailAssign.ass.addElement(sass);
			result.addElement(when);
			result.addElement(headAssign);
			result.addElement(tailAssign);

			return result;
		}
		
		
		@Override
		public Vector broadcast(Channel channel, String channelName, TLAExpr msg, TLAExpr callExp) throws ParseAlgorithmException {
			
			int chan_dim = (channel.dimensions == null) ? 0 : channel.dimensions.size();    
			int callExp_dim =  PcalTLAGen.getCallExprValues(callExp).size();
			
			// compare channel dimension with call expr. incase of mismatch throw exception
			if ( chan_dim < callExp_dim ) {
				throw new ParseAlgorithmException("channel dimension is less than call Expression dimension. ");
			}
			
			if (chan_dim == callExp_dim ) {
				return send(channel, channelName, msg, callExp);
			}
			
			Vector result = new Vector();
			AST.SingleAssign sass = new AST.SingleAssign();
			sass.line = line;
			sass.col  = col;
			sass.lhs.var = channel.var;

			sass.lhs.sub = new TLAExpr(new Vector());
			
			sass.setOrigin(this.getOrigin());
			
			TLAExpr expr = new TLAExpr();
			expr.addLine();    			
			
			ArrayList<String> temp_vars = new ArrayList<>();
			
			for(int i = 0; i < channel.dimensions.size(); i++) {
				String dimension = (String) channel.dimensions.get(i);
				String tempVarName = "_" + dimension.toLowerCase().charAt(0) + i;
				temp_vars.add(tempVarName);
				if(i == 0) {
					expr.addToken(PcalTranslate.BuiltInToken("["));
				}
				expr.addToken(PcalTranslate.IdentToken(tempVarName));
				expr.addToken(PcalTranslate.BuiltInToken(" \\in "));
				expr.addToken(PcalTranslate.IdentToken(dimension));


				if(channel.dimensions.size() != 1 && i != channel.dimensions.size() - 1) {
					expr.addToken(PcalTranslate.BuiltInToken(", "));
				}
			}
		
			expr.addToken(PcalTranslate.BuiltInToken(" |-> "));
			
			if (callExp_dim == 1) {
				expr.addToken(PcalTranslate.BuiltInToken("IF"));
				expr.addToken(PcalTranslate.BuiltInToken(" _n0 = " + callExp.toPlainString().substring(1, callExp.toPlainString().length()-1)));
				expr.addToken(PcalTranslate.BuiltInToken(" THEN "));
				expr.addToken(PcalTranslate.BuiltInToken(" Append("));
				expr.addToken(PcalTranslate.BuiltInToken(channelName + "[_n0, _n1], "));
				
				for(int i = 0; i < msg.tokens.size(); i++) {

		   			Vector tv = (Vector) msg.tokens.elementAt(i);
		   			for (int j = 0; j < tv.size(); j++) {
		   				TLAToken tok = (TLAToken) tv.elementAt(j);

		   				expr.addToken(tok);
		   			}
		   		}
				expr.addToken(PcalTranslate.BuiltInToken(")"));
				
				expr.addToken(PcalTranslate.BuiltInToken(" ELSE "));
				expr.addToken(PcalTranslate.BuiltInToken(channelName + "[_n0, _n1]"));
			} 
			else {
				expr.addToken(PcalTranslate.BuiltInToken(" Append("));
				expr.addToken(PcalTranslate.BuiltInToken(channelName));
				expr.addToken(PcalTranslate.BuiltInToken("["));
				for(int i = 0; i < channel.dimensions.size(); i++) {
					expr.addToken(PcalTranslate.IdentToken(temp_vars.get(i)));
					if(channel.dimensions.size() != 1 && i != channel.dimensions.size() - 1) {
						expr.addToken(PcalTranslate.BuiltInToken(", "));
					}
				}
				
				expr.addToken(PcalTranslate.BuiltInToken("]"));
				expr.addToken(PcalTranslate.BuiltInToken(" , "));			
		   		
		   		for(int i = 0; i < msg.tokens.size(); i++) {

		   			Vector tv = (Vector) msg.tokens.elementAt(i);
		   			for (int j = 0; j < tv.size(); j++) {
		   				TLAToken tok = (TLAToken) tv.elementAt(j);

		   				expr.addToken(tok);
		   			}
		   		}
		   		
		   		expr.addToken(PcalTranslate.BuiltInToken(")"));
			}
			
			expr.addToken(PcalTranslate.BuiltInToken("]"));
			expr.setOrigin(this.getOrigin());
			expr.normalize();

			sass.rhs = expr;

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
		public Vector multicast(Channel channel, String channelName, TLAExpr msg) throws ParseAlgorithmException {

			Vector result = new Vector();

			AST.SingleAssign sass = new AST.SingleAssign();
			sass.line = line;
			sass.col  = col;
			sass.lhs.var = channel.var;

			TLAExpr expr = new TLAExpr();

			sass.lhs.sub = new TLAExpr(new Vector());

			List dimensions = new ArrayList<>(); 
			List dimensionTypes = new ArrayList<>(); 

			TLAExpr thenExp = new TLAExpr();
			thenExp.addLine();

			TLAExpr elseExp = new TLAExpr();
			elseExp.addLine();

			for(int i = 0; i < msg.tokens.size(); i++) {

				Vector tv = (Vector) msg.tokens.elementAt(i);

				for (int j = 0; j < tv.size(); j++) {
					TLAToken tok = (TLAToken) tv.elementAt(j);
					
					if(tok.type == TLAToken.IDENT) {
						
						if(tok.string.equals("self")) {
							dimensions.add(SELF);
							//add to types just to maintain order between the 2 lists
							dimensionTypes.add(SELF);

						} else {
							dimensions.add(tok.string);

							StringBuffer sb = new StringBuffer();
							
							//get the rest of the expression
							tok = (TLAToken) tv.elementAt(++j);
							while(!tok.string.equals(",") && !tok.string.equals("|->")) {
								sb.append(" " + tok.string);
								tok = (TLAToken) tv.elementAt(++j);
							}
							dimensionTypes.add(sb.toString());
						}
					}

					if(tok.string.equals("|->")) {
						//everything after |-> is the expression we want to multicast
						tok = (TLAToken) tv.elementAt(++j);

						//while the next char is , -1 to excluse ] at the end
						while(j < tv.size() - 1) {
							thenExp.addToken((TLAToken) tv.elementAt(j));
							j++;
						}
						break;
					}
				}
			}

			//compare with dimensions within a channel and throw an error if we find a length mismatch
			if(channel.dimensions != null && channel.dimensions.size() != dimensions.size()) {
				throw new ParseAlgorithmException("multicast function expected " + channel.dimensions.size() +" dimentions ");
			}
			
			elseExp.addToken(PcalTranslate.IdentToken(channelName));
			elseExp.addToken(PcalTranslate.IdentToken(dimensions.toString()));

			expr = new TLAExpr();
			expr.addLine();
			expr.addToken(PcalTranslate.BuiltInToken("["));
			if(dimensions.size() == 1) {
				expr.addToken(PcalTranslate.IdentToken(dimensions.toString().substring(1, dimensions.toString().length()-1)));
			} else {
				expr.addToken(PcalTranslate.BuiltInToken("<<"));
				expr.addToken(PcalTranslate.IdentToken(dimensions.toString().substring(1, dimensions.toString().length()-1)));
				expr.addToken(PcalTranslate.BuiltInToken(">>"));
			}
			expr.addToken(PcalTranslate.BuiltInToken(" \\in DOMAIN "));
			expr.addToken(PcalTranslate.IdentToken(channelName));
			expr.addToken(PcalTranslate.BuiltInToken(" |-> "));
			expr.addToken(PcalTranslate.BuiltInToken(" IF "));

			for(int i = 0; i < dimensions.size(); i++) {

				if(dimensions.get(i).equals(SELF)) {
					expr.addToken(PcalTranslate.IdentToken(SELF));
					expr.addToken(PcalTranslate.BuiltInToken(" = self "));
				} else {
					expr.addToken(PcalTranslate.IdentToken(dimensions.get(i).toString()));
					expr.addToken(PcalTranslate.IdentToken(dimensionTypes.get(i).toString()));
				}
				
				if(i != dimensions.size() -1) {
					//fix indentation here, use a stringbuffer and spaceout 
					expr.addLine();
					expr.addToken(PcalTranslate.BuiltInToken(" /\\ "));
				}
			}

			expr.addToken(PcalTranslate.BuiltInToken(" THEN "));

			expr.addLine();
			expr.addToken(PcalTranslate.BuiltInToken(" Append("));

			for(int i = 0; i < elseExp.tokens.size(); i++) {

				Vector tv = (Vector) elseExp.tokens.elementAt(i);
				for (int j = 0; j < tv.size(); j++) {
					TLAToken tok = (TLAToken) tv.elementAt(j);
					expr.addToken(tok);
				}
			}
			
			expr.addToken(PcalTranslate.BuiltInToken(", "));

			for(int i = 0; i < thenExp.tokens.size(); i++) {
				
				Vector tv = (Vector) thenExp.tokens.elementAt(i);
				for (int j = 0; j < tv.size(); j++) {
					TLAToken tok = (TLAToken) tv.elementAt(j);
					tok.column = 0;
					expr.addToken(tok);
				}
			}
			

			expr.addToken(PcalTranslate.BuiltInToken(")"));
			
			expr.addToken(PcalTranslate.BuiltInToken(" ELSE "));

			for(int i = 0; i < elseExp.tokens.size(); i++) {

				Vector tv = (Vector) elseExp.tokens.elementAt(i);
				for (int j = 0; j < tv.size(); j++) {
					TLAToken tok = (TLAToken) tv.elementAt(j);
					expr.addToken(tok);
				}
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
		public Vector clear(Channel channel, String channelName, TLAExpr callExp) throws ParseAlgorithmException {
			Vector result = new Vector();
			
			// For Distributed Pluscal. to build different clear calls depending on the callExp
			int chan_dim = (channel.dimensions == null) ? 0 : channel.dimensions.size();    
			int callExp_dim =  PcalTLAGen.getCallExprValues(callExp).size();
			
			// compare channel dimension with call expr. incase of mismatch throw exception
			if ( chan_dim < callExp_dim ) {
				throw new ParseAlgorithmException("channel dimension is less than call Expression dimension. ");
			}
			
			AST.SingleAssign sass = new AST.SingleAssign();
			sass.line = line;
			sass.col  = col;
			sass.lhs.var = channel.var;
			TLAExpr expr;
			
			if ( chan_dim == callExp_dim ) { // when chan and clear(chan)| chan[N] and clear(chan[self]| chan[N, N] and clear(
				if(callExp.tokens != null)
		   			sass.lhs.sub = callExp;
		   		else
		   			sass.lhs.sub = new TLAExpr(new Vector());
				
				sass.setOrigin(this.getOrigin());

				expr = new TLAExpr();
				expr.addLine();
				
				expr.addToken(PcalTranslate.BuiltInToken("<<"));
				expr.addToken(PcalTranslate.BuiltInToken(">>"));
			}
			else if ( chan_dim != 0 && callExp_dim == 0 ) { // when chan[N] or chan[N,N] and we say clear(chan);
				sass.lhs.sub = new TLAExpr(new Vector());
				sass.setOrigin(this.getOrigin());

				expr = new TLAExpr();
				expr.addLine();
				
				for(int i = 0; i < channel.dimensions.size(); i++) {
					String dimension = (String) channel.dimensions.get(i);
					
					// For Distributed PlusCal. append _ to overcome variable name clash
					String tempVarName = "_" + dimension.toLowerCase().charAt(0) + i;
					
					if(i == 0) {
						expr.addToken(PcalTranslate.BuiltInToken("["));
					}
					expr.addToken(PcalTranslate.IdentToken(tempVarName));
	
					if(channel.dimensions.size() != 1 && i != channel.dimensions.size() - 1) {
						expr.addToken(PcalTranslate.BuiltInToken(", "));
					}
				}

				expr.addToken(PcalTranslate.BuiltInToken(" \\in "));
				expr.addToken(PcalTranslate.IdentToken(channel.dimensions.get(0).toString()));
				expr.addToken(PcalTranslate.BuiltInToken(" |-> "));
				expr.addToken(PcalTranslate.BuiltInToken("<<"));
				expr.addToken(PcalTranslate.BuiltInToken(">>"));

				expr.addToken(PcalTranslate.BuiltInToken("]"));
			}
			else { // when chan[N, N] and clear(chan[self])
				sass.lhs.sub = new TLAExpr(new Vector());
				sass.setOrigin(this.getOrigin());
				expr = new TLAExpr();
				expr.addLine();
				
				for(int i = 0; i < channel.dimensions.size(); i++) {
					String dimension = (String) channel.dimensions.get(i);
					// For Distributed PlusCal. append _ to overcome variable name clash
					String tempVarName = "_" + dimension.toLowerCase().charAt(0) + i;
					
					if(i == 0) {
						expr.addToken(PcalTranslate.BuiltInToken("["));
					}
					expr.addToken(PcalTranslate.IdentToken(tempVarName));

					if(channel.dimensions.size() != 1 && i != channel.dimensions.size() - 1) {
						expr.addToken(PcalTranslate.BuiltInToken(", "));
					}
				}
				
				expr.addToken(PcalTranslate.BuiltInToken(" \\in "));
				expr.addToken(PcalTranslate.IdentToken(channel.dimensions.get(0).toString()));				
				expr.addToken(PcalTranslate.BuiltInToken(" |-> "));
				expr.addToken(PcalTranslate.BuiltInToken(" IF "));
				expr.addToken(PcalTranslate.BuiltInToken("_n0 = " + callExp.toPlainString().substring(1, callExp.toPlainString().length()-1)));
				expr.addToken(PcalTranslate.BuiltInToken(" THEN <<>> "));
				expr.addToken(PcalTranslate.BuiltInToken(" ELSE "));
				expr.addToken(PcalTranslate.BuiltInToken(channelName + "[_n0, _n1]"));

				expr.addToken(PcalTranslate.BuiltInToken("]"));
			}
			
			expr.setOrigin(this.getOrigin());
			expr.normalize();

			sass.rhs = expr;

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
		public Vector sendWithClock(Channel channel, String channelName, TLAExpr msg, TLAExpr callExp, TLAExpr clock) {
			Vector result = new Vector();
	   		
			AST.SingleAssign sass = new AST.SingleAssign();
			sass.line = line;
			sass.col  = col;
			sass.lhs.var = channel.var;

			TLAExpr expr = new TLAExpr();
			
			if(callExp.tokens != null) {
				sass.lhs.sub = callExp;
			}else {
				sass.lhs.sub = new TLAExpr(new Vector());
			}
			
			expr.addLine();
			// dostonbek. Append channel name fix.
			if (! (channel.dimensions == null)) {
				expr.addToken(PcalTranslate.BuiltInToken(" Append(@, "));
			}	else {
				expr.addToken(PcalTranslate.BuiltInToken(" Append(" + channelName + ", "));
			}
			
			expr.addToken(PcalTranslate.BuiltInToken("[msg |-> "));
			for(int i = 0; i < msg.tokens.size(); i++) {
				
				Vector tv = (Vector) msg.tokens.elementAt(i);
				for (int j = 0; j < tv.size(); j++) {
					TLAToken tok = (TLAToken) tv.elementAt(j);

					expr.addToken(tok);
				}
			}
			
			expr.addToken(PcalTranslate.BuiltInToken(", clock |-> "));
			expr.addToken(PcalTranslate.BuiltInToken(clock.toPlainString()));
			expr.addToken(PcalTranslate.BuiltInToken("]"));
			expr.addToken(PcalTranslate.BuiltInToken(")"));
			sass.rhs = expr;

			sass.setOrigin(this.getOrigin());

			AST.Assign assign = new AST.Assign();
			assign.ass = new Vector();
			assign.line = line ;
			assign.col  = col ;
			assign.setOrigin(this.getOrigin());

			assign.ass.addElement(sass);

			result.addElement(assign);
			
			///////////////////////////////
			sass = new AST.SingleAssign();
			sass.line = line;
			sass.col  = col;
			sass.lhs.var = clock.toPlainString();
			
			expr = new TLAExpr();
			
			//if(callExp.tokens != null)
			//sass.lhs.sub = callExp;
			//else
			sass.lhs.sub = new TLAExpr(new Vector());
			
			expr = new TLAExpr();
			expr.addLine();
			expr.addToken(PcalTranslate.IdentToken(clock.toPlainString()));
			
			/*
			if(callExp.tokens != null) {
			for(int i = 0; i < callExp.tokens.size(); i++) {
			
				Vector tv = (Vector) callExp.tokens.elementAt(i);
				for (int j = 0; j < tv.size(); j++) {
					TLAToken tok = (TLAToken) tv.elementAt(j);
			
					expr.addToken(tok);
				}
			}
			}
			*/
			
			expr.addToken(PcalTranslate.BuiltInToken(" + 1 "));
			
			sass.rhs = expr;
			
			sass.setOrigin(this.getOrigin());
			
			assign = new AST.Assign();
			assign.ass = new Vector();
			assign.line = line ;
			assign.col  = col ;
			assign.setOrigin(this.getOrigin());
			
			assign.ass.addElement(sass);
			
			result.addElement(assign);
			
			return result;
		}

		@Override
		public Vector receiveWithClock(Channel channel, String channelName, VarDecl targetVar, TLAExpr callExp,
				TLAExpr targetExp, TLAExpr clock) {
			Vector result = new Vector();
			// For Distributed PlusCal. append _ to overcome variable name clash
			String tempVarName = "_" + channelName.toLowerCase().charAt(0) + line + col;

			TLAExpr exp = new TLAExpr();

			AST.When when = new AST.When();
			when.col = line;
			when.line = col;

			exp = new TLAExpr();
			exp.addLine();

			exp.addToken(PcalTranslate.BuiltInToken("Len("));
			exp.addToken(PcalTranslate.IdentToken(channel.var));
			
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

			when.exp = exp;
			when.setOrigin(this.getOrigin());

			AST.Assign headAssign = new AST.Assign();
			headAssign.ass = new Vector();
			headAssign.line = line ;
			headAssign.col  = col ;
			headAssign.setOrigin(this.getOrigin());
			
			AST.SingleAssign sass = new AST.SingleAssign();
			sass.line = line;
			sass.col  = col;
			sass.lhs.var = targetVar.var;

			TLAExpr expr = new TLAExpr();
      // HC: fix bug FIFO (06/04/21)
			// expr.addLine(); 
			if(targetExp.tokens != null) {
				for(int i = 0; i < targetExp.tokens.size(); i++) {

					Vector tv = (Vector) targetExp.tokens.elementAt(i);
					for (int j = 0; j < tv.size(); j++) {
						TLAToken tok = (TLAToken) tv.elementAt(j);
						expr.addToken(tok);
					}
				}
				sass.lhs.sub = expr;
			} else {
				sass.lhs.sub = new TLAExpr(new Vector());
			}
			
			expr = new TLAExpr();
			expr.addLine();
			expr.addToken(PcalTranslate.BuiltInToken("Head("));
			expr.addToken(PcalTranslate.IdentToken(channel.var));
			
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

			sass.rhs = expr;
			sass.setOrigin(this.getOrigin());

			headAssign.ass.addElement(sass);

			AST.Assign tailAssign = new AST.Assign();
			tailAssign.ass = new Vector();
			tailAssign.line = line ;
			tailAssign.col  = col ;
			tailAssign.setOrigin(this.getOrigin());
			
			sass = new AST.SingleAssign();
			sass.line = line;
			sass.col  = col;
			sass.lhs.var = channel.var;

			if(callExp.tokens != null) {
				sass.lhs.sub = callExp;
			} else {
				sass.lhs.sub = new TLAExpr(new Vector());
			}
			
			expr = new TLAExpr();
			expr.addLine();
			// dm. Receive channel name fix.
			if ( callExp.tokens.size() == 0) {
				expr.addToken(PcalTranslate.BuiltInToken(" Tail(" + channelName + ")"));
			} else {
				expr.addToken(PcalTranslate.BuiltInToken(" Tail(@) "));
			}
			
			sass.rhs = expr;
			
			sass.setOrigin(this.getOrigin());
			tailAssign.ass.addElement(sass);
			
			///////////
			sass = new AST.SingleAssign();
			sass.line = line;
			sass.col  = col;
			sass.lhs.var = clock.toPlainString();
			
			//if(callExp.tokens != null)
				//sass.lhs.sub = callExp;
			//else
				sass.lhs.sub = new TLAExpr(new Vector());
			
			expr = new TLAExpr();
			expr.addLine();
			
			expr.addToken(PcalTranslate.IdentToken("Max("));
			expr.addToken(PcalTranslate.IdentToken(clock.toPlainString()));
			expr.addToken(PcalTranslate.IdentToken(", "));
			String t = targetVar + ".clock";
			expr.addToken(PcalTranslate.IdentToken(t));
			expr.addToken(PcalTranslate.IdentToken(") + 1"));
			
			sass.rhs = expr;
			sass.setOrigin(this.getOrigin());
			AST.Assign assign = new AST.Assign();
			assign.ass = new Vector();
			assign.line = line ;
			assign.col  = col ;
			assign.setOrigin(this.getOrigin());

			assign.ass.addElement(sass);
			/////////////////////////////
			
			result.addElement(when);
			result.addElement(headAssign);
			result.addElement(tailAssign);
			result.addElement(assign);
			
			return result;
		}

		@Override
		public Vector broadcastWithClock(Channel channel, String channelName, TLAExpr msg, TLAExpr callExp,
				TLAExpr clock) throws ParseAlgorithmException {
			int chan_dim = (channel.dimensions == null) ? 0 : channel.dimensions.size();    
			int callExp_dim =  PcalTLAGen.getCallExprValues(callExp).size();
			
			// compare channel dimension with call expr. incase of mismatch throw exception
			if ( chan_dim < callExp_dim ) {
				throw new ParseAlgorithmException("channel dimension is less than call Expression dimension. ");
			}
			
			if (chan_dim == callExp_dim ) {
				return send(channel, channelName, msg, callExp);
			}
			
			Vector result = new Vector();
			AST.SingleAssign sass = new AST.SingleAssign();
			sass.line = line;
			sass.col  = col;
			sass.lhs.var = channel.var;

			sass.lhs.sub = new TLAExpr(new Vector());
			
			sass.setOrigin(this.getOrigin());
			
			TLAExpr expr = new TLAExpr();
			expr.addLine();    			
			
			ArrayList<String> temp_vars = new ArrayList<>();
			
			for(int i = 0; i < channel.dimensions.size(); i++) {
				String dimension = (String) channel.dimensions.get(i);
				String tempVarName = "_" + dimension.toLowerCase().charAt(0) + i;
				temp_vars.add(tempVarName);
				if(i == 0) {
					expr.addToken(PcalTranslate.BuiltInToken("["));
				}
				expr.addToken(PcalTranslate.IdentToken(tempVarName));
				expr.addToken(PcalTranslate.BuiltInToken(" \\in "));
				expr.addToken(PcalTranslate.IdentToken(dimension));


				if(channel.dimensions.size() != 1 && i != channel.dimensions.size() - 1) {
					expr.addToken(PcalTranslate.BuiltInToken(", "));
				}
			}
		
			expr.addToken(PcalTranslate.BuiltInToken(" |-> "));
			
			if (callExp_dim == 1) {
				expr.addToken(PcalTranslate.BuiltInToken("IF"));
				expr.addToken(PcalTranslate.BuiltInToken(" _n0 = " + callExp.toPlainString().substring(1, callExp.toPlainString().length()-1)));
				expr.addToken(PcalTranslate.BuiltInToken(" THEN "));
				expr.addToken(PcalTranslate.BuiltInToken(" Append("));
				expr.addToken(PcalTranslate.BuiltInToken(channelName + "[_n0, _n1], "));
				
				expr.addToken(PcalTranslate.BuiltInToken("[msg |-> "));
				for(int i = 0; i < msg.tokens.size(); i++) {

		   			Vector tv = (Vector) msg.tokens.elementAt(i);
		   			for (int j = 0; j < tv.size(); j++) {
		   				TLAToken tok = (TLAToken) tv.elementAt(j);

		   				expr.addToken(tok);
		   			}
		   		}
				expr.addToken(PcalTranslate.BuiltInToken(", clock |-> "));
				expr.addToken(PcalTranslate.BuiltInToken(clock.toPlainString()));
				expr.addToken(PcalTranslate.BuiltInToken("]"));
				expr.addToken(PcalTranslate.BuiltInToken(")"));
				
				expr.addToken(PcalTranslate.BuiltInToken(" ELSE "));
				expr.addToken(PcalTranslate.BuiltInToken(channelName + "[_n0, _n1]"));
			} 
			else {
				expr.addToken(PcalTranslate.BuiltInToken(" Append("));
				expr.addToken(PcalTranslate.BuiltInToken(channelName));
				expr.addToken(PcalTranslate.BuiltInToken("["));
				for(int i = 0; i < channel.dimensions.size(); i++) {
					expr.addToken(PcalTranslate.IdentToken(temp_vars.get(i)));
					if(channel.dimensions.size() != 1 && i != channel.dimensions.size() - 1) {
						expr.addToken(PcalTranslate.BuiltInToken(", "));
					}
				}
				
				expr.addToken(PcalTranslate.BuiltInToken("]"));
				expr.addToken(PcalTranslate.BuiltInToken(" , "));			
		   		
				expr.addToken(PcalTranslate.BuiltInToken("[msg |-> "));
		   		for(int i = 0; i < msg.tokens.size(); i++) {

		   			Vector tv = (Vector) msg.tokens.elementAt(i);
		   			for (int j = 0; j < tv.size(); j++) {
		   				TLAToken tok = (TLAToken) tv.elementAt(j);

		   				expr.addToken(tok);
		   			}
		   		}
		   		
		   		expr.addToken(PcalTranslate.BuiltInToken(", clock |-> "));
		   		expr.addToken(PcalTranslate.BuiltInToken(clock.toPlainString()));
		   		expr.addToken(PcalTranslate.BuiltInToken("]"));
		   		expr.addToken(PcalTranslate.BuiltInToken(")"));
			}
			
			expr.addToken(PcalTranslate.BuiltInToken("]"));
			expr.setOrigin(this.getOrigin());
			expr.normalize();

			sass.rhs = expr;

			AST.Assign assign = new AST.Assign();
			assign.ass = new Vector();
			assign.line = line ;
			assign.col  = col ;
			assign.setOrigin(this.getOrigin());

			assign.ass.addElement(sass);
			result.addElement(assign);
			
			///////////////////////////////
			sass = new AST.SingleAssign();
			sass.line = line;
			sass.col  = col;
			sass.lhs.var = clock.toPlainString();
			
			expr = new TLAExpr();
			
			//if(callExp.tokens != null)
			//sass.lhs.sub = callExp;
			//else
			sass.lhs.sub = new TLAExpr(new Vector());
			
			expr = new TLAExpr();
			expr.addLine();
			expr.addToken(PcalTranslate.IdentToken(clock.toPlainString()));
			
			/*
			if(callExp.tokens != null) {
			for(int i = 0; i < callExp.tokens.size(); i++) {
			
			Vector tv = (Vector) callExp.tokens.elementAt(i);
			for (int j = 0; j < tv.size(); j++) {
				TLAToken tok = (TLAToken) tv.elementAt(j);
			
				expr.addToken(tok);
			}
			}
			}
			*/
			
			expr.addToken(PcalTranslate.BuiltInToken(" + 1 "));
			
			sass.rhs = expr;
			
			sass.setOrigin(this.getOrigin());
			
			assign = new AST.Assign();
			assign.ass = new Vector();
			assign.line = line ;
			assign.col  = col ;
			assign.setOrigin(this.getOrigin());
			
			assign.ass.addElement(sass);
			
			result.addElement(assign);
			
			return result;
		}
   }
   
   public static class ChannelSendCall extends AST{
    public String name = "";
   	public String channelName = "";
    public TLAExpr callExp = new TLAExpr(new Vector());
	public TLAExpr msg = null;
   	public Boolean isBroadcast = false;
   	public Boolean isMulticast = false;
   	
   	public ChannelSendCall() {};
   	public String toString()
   	{ return 
   			Indent(lineCol()) + 
   			"[type |-> \"ChannelSender\"," + NewLine() +
   			" name |-> \"" + name + "\"," + NewLine() +
   			Indent(" channel     |-> ") + channelName + "]" +
   			EndIndent() + NewLine() +
   			Indent(" msg     |-> ") + msg + "]" +
   			EndIndent() +
   			Indent(" callExp     |-> ") + callExp + "]" +
   			EndIndent() +
   			EndIndent() ;
   	}
   	
   	/**
 	 * generates the body for a send call
 	 * @param channel
 	 * @return
 	 */
	public Vector generateBodyTemplate(Channel channel) {
			return channel.send(channel, channelName, msg, callExp);
	}
	
	/**
	 * 
	 * @param channel
	 * @return
	 * @throws ParseAlgorithmException 
	 */
	public Vector generateBroadcastBodyTemplate(Channel channel) throws ParseAlgorithmException {
		return channel.broadcast(channel, channelName, msg, callExp);
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
	   public String name = "";
	   public String channelName = "";
	   public TLAExpr callExp = new TLAExpr(new Vector());
	   public Vector args;
	   String targetVarName = "";
	   public TLAExpr targetExp = new TLAExpr(new Vector());
	   public ChannelReceiveCall() {};
	   public String toString()
	   { return 
			   Indent(lineCol()) + 
			   "[type |-> \"ChannelReceiver\"," + NewLine() +
			   Indent(" channel     |-> ") + channelName + "," +
			   EndIndent() +
			   Indent(" targetVar     |-> ") + targetVarName + "," +
			   EndIndent() +
			   Indent(" callExp     |-> ") + callExp + "," +
			   EndIndent() +
			   Indent(" targetExp     |-> ") + targetExp + "]" +
			   EndIndent() +
			   EndIndent() ;
	   }

	   public Vector generateBodyTemplate(Channel channel, VarDecl targetVar) {
		   return channel.receive(channel, channelName, targetVar, callExp, targetExp);
	   }
	   
   }

   
   public static class ChannelClearCall extends AST{
	   public String name = "";
	   public String channelName = "";
	   public TLAExpr callExp = new TLAExpr(new Vector());
	   public String type;
	   public ChannelClearCall() {};
	   
	   public String toString()
	   { return 
			   Indent(lineCol()) + 
			   "[type |-> \"ChannelClearCall\"," + NewLine() +
			   Indent(" channel     |-> ") + channelName + "]" +
			   EndIndent() +
			   EndIndent() ;
	   }

	   public Vector generateBodyTemplate(Channel channel) throws ParseAlgorithmException {
		   return channel.clear(channel, channelName, callExp);
	   }
	   
   }
   
   // For Distributed PlusCal. Channel operations with logical clocks
   public static class ChannelSendWithClockCall extends AST{
	    public String name = "";
	   	public String channelName = "";
	    public TLAExpr callExp = new TLAExpr(new Vector());
		public TLAExpr msg = null;
	   	public Boolean isBroadcast = false;
	   	public Boolean isMulticast = false;
	   	public TLAExpr clock = null;
	   	
	   	public ChannelSendWithClockCall() {};
	   	public String toString()
	   	{ return 
	   			Indent(lineCol()) + 
	   			"[type |-> \"ChannelSender\"," + NewLine() +
	   			" name |-> \"" + name + "\"," + NewLine() +
	   			Indent(" channel     |-> ") + channelName + "]" +
	   			EndIndent() + NewLine() +
	   			Indent(" msg     |-> ") + msg + "]" +
	   			EndIndent() +
	   			Indent(" callExp     |-> ") + callExp + "]" +
	   			EndIndent() +
	   			Indent(" clock     |-> ") + clock + "]" +
	   			EndIndent() +
	   			EndIndent() ;
	   	}
	   	
	   	/**
	 	 * generates the body for a send call
	 	 * @param channel
	 	 * @return
	 	 */
		public Vector generateBodyWithClockTemplate(Channel channel) {
				return channel.sendWithClock(channel, channelName, msg, callExp, clock);
		}
		
		/**
		 * 
		 * @param channel
		 * @return
		 * @throws ParseAlgorithmException 
		 */
		public Vector generateBroadcastWithClockBodyTemplate(Channel channel) throws ParseAlgorithmException {
			return channel.broadcastWithClock(channel, channelName, msg, callExp, clock);
		}
		
		/**
		 * @param channel
		 * @return
		 * @throws ParseAlgorithmException 
		 */
		// Need to think about multicast implementation with logical clocks. QUESTION
		public Vector generateMulticastBodyTemplate(Channel channel) throws ParseAlgorithmException {
			return channel.multicast(channel, channelName, msg);
		}

	   }
   
   public static class ChannelReceiveWithClockCall extends AST{
	   public String name = "";
	   public String channelName = "";
	   public TLAExpr callExp = new TLAExpr(new Vector());
	   public Vector args;
	   String targetVarName = "";
	   public TLAExpr targetExp = new TLAExpr(new Vector());
	   
	   public TLAExpr clock = null;
	   
	   public ChannelReceiveWithClockCall() {};
	   public String toString()
	   { return 
			   Indent(lineCol()) + 
			   "[type |-> \"ChannelReceiver\"," + NewLine() +
			   Indent(" channel     |-> ") + channelName + "," +
			   EndIndent() +
			   Indent(" targetVar     |-> ") + targetVarName + "," +
			   EndIndent() +
			   Indent(" callExp     |-> ") + callExp + "," +
			   EndIndent() +
			   Indent(" targetExp     |-> ") + targetExp + "]" +
			   EndIndent() +
			   EndIndent() ;
	   }

	   public Vector generateBodyTemplate(Channel channel, VarDecl targetVar) {
		   return channel.receiveWithClock(channel, channelName, targetVar, callExp, targetExp, clock);
	   }
	   
   }
   
  
  public static class Thread extends AST{
	  public String    name  = "" ;
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
				  "\", minusLabels |-> "
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
  
  // For Distributed Pluscal. Clocks
  public static abstract class Clock extends VarDecl{

	   	public Clock() {};
	   	List dimensions = null;
	   	public abstract Vector increase(Clock clock, String clockName, TLAExpr callExp) throws ParseAlgorithmException;
	   	public abstract Vector update(Clock clock1, String clockName1, TLAExpr callExp1, Clock clock2, String clockName2, TLAExpr callExp2) throws ParseAlgorithmException;
	   	public abstract Vector reset(Clock clock, String clockName, TLAExpr callExp) throws ParseAlgorithmException;
  }
  
  public static class ClockIncreaseCall extends AST{
	   public String name = "";
	   public Channel clock = null;
	   public String clockName = null;
	   
	   // For Distributed PLuscal. to support increase(clock[N])...
	   public TLAExpr callExp = new TLAExpr(new Vector());
	   
	   public ClockIncreaseCall() {};

	   public String toString()
	   { return 
			   Indent(lineCol()) + 
			   "[type |-> \"ClockIncreaseCall\"," + NewLine() +
			   Indent(" clock     |-> ") + clockName + "]" +
			   EndIndent() +
			   EndIndent() ;
	   }

	   public Vector generateClockIncreaseTemplate(Clock clock) throws ParseAlgorithmException {
		   return clock.increase(clock, clockName, callExp);
	   }
  }
  
  public static class ClockUpdateCall extends AST{
	   public String name1 = "";
	   public Channel clock1 = null;
	   public String clockName1 = null;
	   public String name2 = "";
	   public Channel clock2 = null;
	   public String clockName2 = null;
	   
	   // For Distributed PLuscal. NEED TO THINK ABOUT : update(clock[self], clock[self-1]) ??? how to handle it
	   public TLAExpr callExp1 = new TLAExpr(new Vector());
	   public TLAExpr callExp2 = new TLAExpr(new Vector());
	   
	   public ClockUpdateCall() {};
	   
	   public String toString()
	   { return 
			   Indent(lineCol()) + 
			   "[type |-> \"ClockUpdateCall\"," + NewLine() +
			   Indent(" clock1    |-> ") + clockName1 + "]" +
			   Indent(" clock2    |-> ") + clockName2 + "]" + 
			   EndIndent() +
			   EndIndent() ;
	   }

	   public Vector generateClockUpdateTemplate(Clock clock1, Clock clock2) throws ParseAlgorithmException {
		   return clock1.update(clock1, clockName1, callExp1, clock2, clockName2, callExp2);
	   }
  }
  
  public static class ClockResetCall extends AST{
	   public String name = "";
	   public Channel clock = null;
	   public String clockName = null;
	   
	   // For Distributed PLuscal. to support increase(clock[N])...
	   public TLAExpr callExp = new TLAExpr(new Vector());
	   
	   public ClockResetCall() {};

	   public String toString()
	   { return 
			   Indent(lineCol()) + 
			   "[type |-> \"ClockResetCall\"," + NewLine() +
			   Indent(" clock     |-> ") + clockName + "]" +
			   EndIndent() +
			   EndIndent() ;
	   }

	   public Vector generateClockResetTemplate(Clock clock) throws ParseAlgorithmException {
		   return clock.reset(clock, clockName, callExp);
	   }
 }
  
  public static class LamportClock extends Clock {
	  
	public LamportClock() {};  
	  
	@Override
	public Vector increase(Clock clock, String clockName, TLAExpr callExp) throws ParseAlgorithmException{
		Vector result = new Vector();

   		AST.SingleAssign sass = new AST.SingleAssign();
   		sass.line = line;
   		sass.col  = col;
   		sass.lhs.var = clock.var;

   		TLAExpr expr = new TLAExpr();

   		if(callExp.tokens != null)
   			sass.lhs.sub = callExp;
   		else
   			sass.lhs.sub = new TLAExpr(new Vector());
   		
   		expr = new TLAExpr();
   		expr.addLine();
   		expr.addToken(PcalTranslate.IdentToken(clockName));
   		
   		if(callExp.tokens != null) {
   			for(int i = 0; i < callExp.tokens.size(); i++) {

   				Vector tv = (Vector) callExp.tokens.elementAt(i);
   				for (int j = 0; j < tv.size(); j++) {
   					TLAToken tok = (TLAToken) tv.elementAt(j);

   					expr.addToken(tok);
   				}
   			}
   		}
   		
   		expr.addToken(PcalTranslate.BuiltInToken(" + 1 "));
   		
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
	public Vector update(Clock clock1, String clockName1, TLAExpr callExp1, Clock clock2, String clockName2, TLAExpr callExp2) throws ParseAlgorithmException {
		Vector result = new Vector();
		
   		AST.SingleAssign sass = new AST.SingleAssign();
   		sass.line = line;
   		sass.col  = col;
   		sass.lhs.var = clock1.var;

   		TLAExpr expr = new TLAExpr();

   		if(callExp1.tokens != null)
   			sass.lhs.sub = callExp1;
   		else
   			sass.lhs.sub = new TLAExpr(new Vector());
   		
   		expr = new TLAExpr();
   		expr.addLine();

   		expr.addToken(PcalTranslate.BuiltInToken(" Max("));
   		expr.addToken(PcalTranslate.IdentToken(clockName1));

   		if(callExp1.tokens != null) {
   			for(int i = 0; i < callExp1.tokens.size(); i++) {

   				Vector tv = (Vector) callExp1.tokens.elementAt(i);
   				for (int j = 0; j < tv.size(); j++) {
   					TLAToken tok = (TLAToken) tv.elementAt(j);

   					expr.addToken(tok);
   				}
   			}
   		}
   		
   		expr.addToken(PcalTranslate.BuiltInToken(", "));
   		expr.addToken(PcalTranslate.IdentToken(clockName2));
   		
   		if(callExp2.tokens != null) {
   			for(int i = 0; i < callExp2.tokens.size(); i++) {

   				Vector tv = (Vector) callExp2.tokens.elementAt(i);
   				for (int j = 0; j < tv.size(); j++) {
   					TLAToken tok = (TLAToken) tv.elementAt(j);

   					expr.addToken(tok);
   				}
   			}
   		}
   		
   		expr.addToken(PcalTranslate.BuiltInToken(") + 1"));
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
	public Vector reset(Clock clock, String clockName, TLAExpr callExp) throws ParseAlgorithmException {
		Vector result = new Vector();
		 
		int clock_dim = (clock.dimensions == null) ? 0 : clock.dimensions.size();
		int callExp_dim = PcalTLAGen.getCallExprValues(callExp).size();
		
		if ( clock_dim < callExp_dim ) {
			throw new ParseAlgorithmException("clock dimension is less than call Expression dimension. ");
		}
		
		AST.SingleAssign sass = new AST.SingleAssign();
		sass.line = line;
		sass.col  = col;
		sass.lhs.var = clock.var;
		TLAExpr expr;
		
		if (clock_dim == callExp_dim) {
			if(callExp.tokens != null)
	   			sass.lhs.sub = callExp;
	   		else
	   			sass.lhs.sub = new TLAExpr(new Vector());
	   		
			sass.setOrigin(this.getOrigin());

			expr = new TLAExpr();
			expr.addLine();
			
			expr.addToken(PcalTranslate.BuiltInToken("0"));
		} else {
			sass.lhs.sub = new TLAExpr(new Vector());
			sass.setOrigin(this.getOrigin());

			expr = new TLAExpr();
			expr.addLine();
			
			for(int i = 0; i < clock.dimensions.size(); i++) {
				String dimension = (String) clock.dimensions.get(i);
				// For Distributed PlusCal. append _ to overcome variable name clash
				String tempVarName = String.valueOf("_" + dimension.toLowerCase().charAt(0)) + i;
				
				if(i == 0) {
					expr.addToken(PcalTranslate.BuiltInToken("["));
				}
				expr.addToken(PcalTranslate.IdentToken(tempVarName));

				if(clock.dimensions.size() != 1 && i != clock.dimensions.size() - 1) {
					expr.addToken(PcalTranslate.BuiltInToken(", "));
				}
			}

			expr.addToken(PcalTranslate.BuiltInToken(" \\in "));
			expr.addToken(PcalTranslate.IdentToken(clock.dimensions.get(0).toString()));
			expr.addToken(PcalTranslate.BuiltInToken(" |-> "));
			expr.addToken(PcalTranslate.BuiltInToken("0 "));
			expr.addToken(PcalTranslate.BuiltInToken("] "));
		}
		
		expr.setOrigin(this.getOrigin());
		expr.normalize();

		sass.rhs = expr;

		AST.Assign assign = new AST.Assign();
		assign.ass = new Vector();
		assign.line = line ;
		assign.col  = col ;
		assign.setOrigin(this.getOrigin());
		assign.ass.addElement(sass);

		result.addElement(assign);
		
		return result;
	}
	  
  }
  
  public static class VectorClock extends Clock {
	  
		public VectorClock() {};  
		  
		@Override
		public Vector increase(Clock clock, String clockName, TLAExpr callExp) {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public Vector update(Clock clock1, String clockName1, TLAExpr callExp1, Clock clock2, String clockName2, TLAExpr callExp2) {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public Vector reset(Clock clock, String clockName, TLAExpr callExp) {
			// TODO Auto-generated method stub
			return null;
		}
		  
	  }
  

 }
