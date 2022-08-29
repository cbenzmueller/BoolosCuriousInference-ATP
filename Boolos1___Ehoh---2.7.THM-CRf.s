%------------------------------------------------------------------------------
% File     : Ehoh---2.7
% Problem  : theBenchmark.p : TPTP v0.0.0. Released v0.0.0.
% Transfm  : none
% Format   : tptp:raw
% Command  : eprover-ho %s --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --free-numbers -auto-schedule -p --cpu-limit=%d --neg-ext=all --pos-ext=all --ext-sup-max-depth=2 --schedule-kind=CASC

% Computer : n015.cluster.edu
% Model    : x86_64 x86_64
% CPU      : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory   : 8042.1875MB
% OS       : Linux 3.10.0-693.el7.x86_64
% CPULimit : 300s
% WCLimit  : 300s
% DateTime : Mon Aug  1 10:14:12 EDT 2022

% Result   : Theorem 149.67s 150.15s
% Output   : CNFRefutation 149.67s
% Verified : 
% SZS Type : -

% Comments : 
%------------------------------------------------------------------------------
%----WARNING: Could not form TPTP format derivation
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.15  % Problem    : theBenchmark.p : TPTP v0.0.0. Released v0.0.0.
% 0.03/0.16  % Command    : eprover-ho %s --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --free-numbers -auto-schedule -p --cpu-limit=%d --neg-ext=all --pos-ext=all --ext-sup-max-depth=2 --schedule-kind=CASC
% 0.12/0.38  Computer   : n015.cluster.edu
% 0.12/0.38  Model      : x86_64 x86_64
% 0.12/0.38  CPUModel   : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.38  RAMPerCPU  : 8042.1875MB
% 0.12/0.38  OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.38  % CPULimit   : 300
% 0.12/0.38  % WCLimit    : 300
% 0.12/0.38  % DateTime   : Mon Aug  1 10:38:03 EDT 2022
% 0.19/0.38  % CPUTime    : 
% 0.19/0.39  % Number of cores: 8
% 0.19/0.39  % Python version: Python 3.6.8
% 0.19/0.39  # Version: 2.6rc1-ho
% 0.19/0.39  # No SInE strategy applied
% 0.19/0.39  # Trying AutoSched0 for 149 seconds
% 149.16/149.61  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 149.16/149.61  # and selection function SelectComplexExceptUniqMaxHorn.
% 149.16/149.61  #
% 149.16/149.61  # Preprocessing time       : 0.055 s
% 149.16/149.61  # Presaturation interreduction done
% 149.19/149.70  # No success with AutoSched0
% 149.19/149.70  # Trying AutoSched1 for 65 seconds
% 149.67/150.15  # AutoSched1-Mode selected heuristic G_E___301_C18_F1_URBAN_S5PRR_S0Y
% 149.67/150.15  # and selection function SelectMaxLComplexAvoidPosPred.
% 149.67/150.15  #
% 149.67/150.15  # Preprocessing time       : 0.029 s
% 149.67/150.15  
% 149.67/150.15  # Proof found!
% 149.67/150.15  # SZS status Theorem
% 149.67/150.15  # SZS output start CNFRefutation
% 149.67/150.15  thf(p_def, axiom, (p)=(^[X3:$i, X2:$i]:$@_var @ (^[X5:$i]:![X6:$i > $o]:(isIndSet @ X6=>X6 @ X5)) @ (f @ X3 @ X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', p_def)).
% 149.67/150.15  thf(isIndSet_def, axiom, (isIndSet)=(^[X4:$i > $o]:(X4 @ e&![X3:$i]:(X4 @ X3=>X4 @ (s @ X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', isIndSet_def)).
% 149.67/150.15  thf(a1, axiom, ![X1:$i]:(f @ X1 @ e)=(s @ e), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', a1)).
% 149.67/150.15  thf(a2, axiom, ![X2:$i]:(f @ e @ (s @ X2))=(s @ (s @ (f @ e @ X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', a2)).
% 149.67/150.15  thf(a3, axiom, ![X3:$i, X2:$i]:(f @ (s @ X3) @ (s @ X2))=(f @ X3 @ (f @ (s @ X3) @ X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', a3)).
% 149.67/150.15  thf(a5, axiom, ![X3:$i]:(d @ X3=>d @ (s @ X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', a5)).
% 149.67/150.15  thf(a4, axiom, d @ e, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', a4)).
% 149.67/150.15  thf(conj_0, conjecture, d @ (f @ (s @ (s @ (s @ (s @ e)))) @ (s @ (s @ (s @ (s @ e))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', conj_0)).
% 149.67/150.15  thf(c_0_8, plain, ![X3:$i, X2:$i]:(p @ X3 @ X2<=>![X14:$i > $o]:(isIndSet @ X14=>X14 @ (f @ X3 @ X2))), inference(fof_simplification,[status(thm)],[p_def])).
% 149.67/150.15  thf(c_0_9, plain, ![X4:$i > $o]:(isIndSet @ X4<=>(X4 @ e&![X12:$i]:(X4 @ X12=>X4 @ (s @ X12)))), inference(fof_simplification,[status(thm)],[isIndSet_def])).
% 149.67/150.15  thf(c_0_10, plain, ![X24:$i, X25:$i, X26:$i > $o, X27:$i, X28:$i]:((~p @ X24 @ X25|(~isIndSet @ X26|X26 @ (f @ X24 @ X25)))&((isIndSet @ (epred1_2 @ X27 @ X28)|p @ X27 @ X28)&(~epred1_2 @ X27 @ X28 @ (f @ X27 @ X28)|p @ X27 @ X28))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])])])])).
% 149.67/150.15  thf(c_0_11, plain, ![X15:$i]:(f @ X15 @ e)=(s @ e), inference(variable_rename,[status(thm)],[a1])).
% 149.67/150.15  thf(c_0_12, plain, ![X20:$i > $o, X21:$i, X22:$i > $o]:(((X20 @ e|~isIndSet @ X20)&(~X20 @ X21|X20 @ (s @ X21)|~isIndSet @ X20))&((X22 @ (esk1_1 @ X22)|~X22 @ e|isIndSet @ X22)&(~X22 @ (s @ (esk1_1 @ X22))|~X22 @ e|isIndSet @ X22))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])])])])).
% 149.67/150.15  thf(c_0_13, plain, ![X1:$i, X2:$i]:(p @ X1 @ X2|~epred1_2 @ X1 @ X2 @ (f @ X1 @ X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 149.67/150.15  thf(c_0_14, plain, ![X1:$i]:(f @ X1 @ e)=(s @ e), inference(split_conjunct,[status(thm)],[c_0_11])).
% 149.67/150.15  thf(c_0_15, plain, ![X1:$i, X4:$i > $o]:(X4 @ (s @ X1)|~X4 @ X1|~isIndSet @ X4), inference(split_conjunct,[status(thm)],[c_0_12])).
% 149.67/150.15  thf(c_0_16, plain, ![X1:$i, X2:$i]:(isIndSet @ (epred1_2 @ X1 @ X2)|p @ X1 @ X2), inference(split_conjunct,[status(thm)],[c_0_10])).
% 149.67/150.15  thf(c_0_17, plain, ![X4:$i > $o]:(X4 @ e|~isIndSet @ X4), inference(split_conjunct,[status(thm)],[c_0_12])).
% 149.67/150.15  thf(c_0_18, plain, ![X1:$i]:(p @ X1 @ e|~epred1_2 @ X1 @ e @ (s @ e)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 149.67/150.15  thf(c_0_19, plain, ![X1:$i, X2:$i, X3:$i]:(epred1_2 @ X1 @ X2 @ (s @ X3)|p @ X1 @ X2|~epred1_2 @ X1 @ X2 @ X3), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 149.67/150.15  thf(c_0_20, plain, ![X1:$i, X2:$i]:(epred1_2 @ X1 @ X2 @ e|p @ X1 @ X2), inference(spm,[status(thm)],[c_0_17, c_0_16])).
% 149.67/150.15  thf(c_0_21, plain, ![X16:$i]:(f @ e @ (s @ X16))=(s @ (s @ (f @ e @ X16))), inference(variable_rename,[status(thm)],[a2])).
% 149.67/150.15  thf(c_0_22, plain, ![X1:$i, X2:$i, X4:$i > $o]:(X4 @ (f @ X1 @ X2)|~p @ X1 @ X2|~isIndSet @ X4), inference(split_conjunct,[status(thm)],[c_0_10])).
% 149.67/150.15  thf(c_0_23, plain, ![X4:$i > $o]:(X4 @ (esk1_1 @ X4)|isIndSet @ X4|~X4 @ e), inference(split_conjunct,[status(thm)],[c_0_12])).
% 149.67/150.15  thf(c_0_24, plain, ![X1:$i]:p @ X1 @ e, inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_20])).
% 149.67/150.15  thf(c_0_25, plain, ![X1:$i]:(f @ e @ (s @ X1))=(s @ (s @ (f @ e @ X1))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 149.67/150.15  thf(c_0_26, plain, ![X1:$i, X4:$i > $o]:(X4 @ (f @ X1 @ (esk1_1 @ (p @ X1)))|isIndSet @ (p @ X1)|~isIndSet @ X4), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24])])).
% 149.67/150.15  thf(c_0_27, plain, ![X17:$i, X18:$i]:(f @ (s @ X17) @ (s @ X18))=(f @ X17 @ (f @ (s @ X17) @ X18)), inference(variable_rename,[status(thm)],[a3])).
% 149.67/150.15  thf(c_0_28, plain, (f @ e @ (s @ e))=(s @ (s @ (s @ e))), inference(spm,[status(thm)],[c_0_25, c_0_14])).
% 149.67/150.15  thf(c_0_29, plain, ![X1:$i, X2:$i, X4:$i > $o]:(X4 @ (f @ X1 @ (f @ X2 @ (esk1_1 @ (p @ X2))))|isIndSet @ (p @ X2)|~isIndSet @ (p @ X1)|~isIndSet @ X4), inference(spm,[status(thm)],[c_0_22, c_0_26])).
% 149.67/150.15  thf(c_0_30, plain, ![X1:$i, X2:$i]:(f @ (s @ X1) @ (s @ X2))=(f @ X1 @ (f @ (s @ X1) @ X2)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 149.67/150.15  thf(c_0_31, plain, ![X1:$i, X2:$i, X3:$i]:(epred1_2 @ X1 @ X2 @ (f @ e @ (s @ X3))|p @ X1 @ X2|~epred1_2 @ X1 @ X2 @ (s @ (f @ e @ X3))), inference(spm,[status(thm)],[c_0_19, c_0_25])).
% 149.67/150.15  thf(c_0_32, plain, (p @ e @ (s @ e)|~epred1_2 @ e @ (s @ e) @ (s @ (s @ (s @ e)))), inference(spm,[status(thm)],[c_0_13, c_0_28])).
% 149.67/150.15  thf(c_0_33, plain, ![X1:$i, X4:$i > $o]:(X4 @ (f @ (s @ X1) @ (s @ (esk1_1 @ (p @ (s @ X1)))))|isIndSet @ (p @ (s @ X1))|~isIndSet @ (p @ X1)|~isIndSet @ X4), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 149.67/150.15  thf(c_0_34, plain, ![X1:$i]:(p @ e @ (s @ X1)|~epred1_2 @ e @ (s @ X1) @ (s @ (f @ e @ X1))), inference(spm,[status(thm)],[c_0_13, c_0_31])).
% 149.67/150.15  thf(c_0_35, plain, (p @ e @ (s @ e)|~epred1_2 @ e @ (s @ e) @ (s @ (s @ e))), inference(spm,[status(thm)],[c_0_32, c_0_19])).
% 149.67/150.15  thf(c_0_36, plain, ![X4:$i > $o]:(X4 @ (s @ e)|~isIndSet @ X4), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_24]), c_0_14])).
% 149.67/150.15  thf(c_0_37, plain, ![X4:$i > $o]:(isIndSet @ X4|~X4 @ (s @ (esk1_1 @ X4))|~X4 @ e), inference(split_conjunct,[status(thm)],[c_0_12])).
% 149.67/150.15  thf(c_0_38, plain, ![X1:$i]:(p @ (s @ X1) @ (s @ (esk1_1 @ (p @ (s @ X1))))|isIndSet @ (p @ (s @ X1))|~isIndSet @ (p @ X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_33]), c_0_16])).
% 149.67/150.15  thf(c_0_39, plain, ![X1:$i]:(p @ e @ (s @ X1)|~epred1_2 @ e @ (s @ X1) @ (f @ e @ X1)), inference(spm,[status(thm)],[c_0_34, c_0_19])).
% 149.67/150.15  thf(c_0_40, plain, (p @ e @ (s @ e)|~epred1_2 @ e @ (s @ e) @ (s @ e)), inference(spm,[status(thm)],[c_0_35, c_0_19])).
% 149.67/150.15  thf(c_0_41, plain, ![X1:$i, X2:$i]:(epred1_2 @ X1 @ X2 @ (s @ e)|p @ X1 @ X2), inference(spm,[status(thm)],[c_0_36, c_0_16])).
% 149.67/150.15  thf(c_0_42, plain, ![X1:$i]:(isIndSet @ (p @ (s @ X1))|~isIndSet @ (p @ X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_24])])).
% 149.67/150.15  thf(c_0_43, plain, (p @ e @ (s @ (esk1_1 @ (p @ e)))|isIndSet @ (p @ e)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_26]), c_0_16])).
% 149.67/150.15  thf(c_0_44, plain, p @ e @ (s @ e), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 149.67/150.15  thf(c_0_45, plain, ![X2:$i, X1:$i]:(p @ (s @ X1) @ (s @ X2)|~p @ (s @ X1) @ X2|~isIndSet @ (p @ X1)), inference(spm,[status(thm)],[c_0_15, c_0_42])).
% 149.67/150.15  thf(c_0_46, plain, isIndSet @ (p @ e), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_43]), c_0_24])])).
% 149.67/150.15  thf(c_0_47, plain, ![X4:$i > $o]:(X4 @ (s @ (s @ (s @ e)))|~isIndSet @ X4), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_44]), c_0_28])).
% 149.67/150.15  thf(c_0_48, plain, ![X1:$i]:(p @ (s @ e) @ (s @ X1)|~p @ (s @ e) @ X1), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 149.67/150.15  thf(c_0_49, plain, ![X1:$i]:(p @ X1 @ (esk1_1 @ (p @ X1))|isIndSet @ (p @ X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_26]), c_0_16])).
% 149.67/150.15  thf(c_0_50, plain, ![X1:$i]:(p @ (s @ X1) @ (s @ (s @ (s @ e)))|~isIndSet @ (p @ X1)), inference(spm,[status(thm)],[c_0_47, c_0_42])).
% 149.67/150.15  thf(c_0_51, plain, isIndSet @ (p @ (s @ e)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_48]), c_0_24])]), c_0_49])).
% 149.67/150.15  thf(c_0_52, plain, ![X1:$i, X4:$i > $o]:(X4 @ (f @ (s @ X1) @ (s @ (s @ (s @ e))))|~isIndSet @ (p @ X1)|~isIndSet @ X4), inference(spm,[status(thm)],[c_0_22, c_0_50])).
% 149.67/150.15  thf(c_0_53, plain, ![X1:$i]:(p @ (s @ (s @ e)) @ (s @ X1)|~p @ (s @ (s @ e)) @ X1), inference(spm,[status(thm)],[c_0_45, c_0_51])).
% 149.67/150.15  thf(c_0_54, plain, ![X2:$i, X1:$i]:(p @ (s @ (s @ X1)) @ (s @ X2)|~p @ (s @ (s @ X1)) @ X2|~isIndSet @ (p @ X1)), inference(spm,[status(thm)],[c_0_45, c_0_42])).
% 149.67/150.15  thf(c_0_55, plain, ![X1:$i, X4:$i > $o]:(X4 @ (f @ (s @ (s @ X1)) @ (s @ (s @ (s @ e))))|~isIndSet @ (p @ X1)|~isIndSet @ X4), inference(spm,[status(thm)],[c_0_52, c_0_42])).
% 149.67/150.15  thf(c_0_56, plain, isIndSet @ (p @ (s @ (s @ e))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_53]), c_0_24])]), c_0_49])).
% 149.67/150.15  thf(c_0_57, plain, ![X19:$i]:(~d @ X19|d @ (s @ X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[a5])])).
% 149.67/150.15  thf(c_0_58, plain, ![X2:$i, X1:$i]:(p @ (s @ (s @ (s @ X1))) @ (s @ X2)|~p @ (s @ (s @ (s @ X1))) @ X2|~isIndSet @ (p @ X1)), inference(spm,[status(thm)],[c_0_54, c_0_42])).
% 149.67/150.15  thf(c_0_59, plain, ![X4:$i > $o]:(X4 @ (f @ (s @ (s @ (s @ (s @ e)))) @ (s @ (s @ (s @ e))))|~isIndSet @ X4), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 149.67/150.15  thf(c_0_60, plain, ![X1:$i]:(d @ (s @ X1)|~d @ X1), inference(split_conjunct,[status(thm)],[c_0_57])).
% 149.67/150.15  thf(c_0_61, plain, d @ e, inference(split_conjunct,[status(thm)],[a4])).
% 149.67/150.15  thf(c_0_62, negated_conjecture, ~d @ (f @ (s @ (s @ (s @ (s @ e)))) @ (s @ (s @ (s @ (s @ e))))), inference(fof_simplification,[status(thm)],[inference(assume_negation,[status(cth)],[conj_0])])).
% 149.67/150.15  thf(c_0_63, plain, ![X1:$i, X2:$i, X4:$i > $o]:(X4 @ (f @ (s @ (s @ (s @ X1))) @ (s @ X2))|~p @ (s @ (s @ (s @ X1))) @ X2|~isIndSet @ (p @ X1)|~isIndSet @ X4), inference(spm,[status(thm)],[c_0_22, c_0_58])).
% 149.67/150.15  thf(c_0_64, plain, p @ (s @ (s @ (s @ (s @ e)))) @ (s @ (s @ (s @ e))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_59]), c_0_16])).
% 149.67/150.15  thf(c_0_65, plain, (isIndSet @ d|~d @ (esk1_1 @ d)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_60]), c_0_61])])).
% 149.67/150.15  thf(c_0_66, negated_conjecture, ~d @ (f @ (s @ (s @ (s @ (s @ e)))) @ (s @ (s @ (s @ (s @ e))))), inference(split_conjunct,[status(thm)],[c_0_62])).
% 149.67/150.15  thf(c_0_67, plain, ![X4:$i > $o]:(X4 @ (f @ (s @ (s @ (s @ (s @ e)))) @ (s @ (s @ (s @ (s @ e)))))|~isIndSet @ X4), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_51])])).
% 149.67/150.15  thf(c_0_68, plain, isIndSet @ d, inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_23]), c_0_61])])).
% 149.67/150.15  thf(c_0_69, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_68])]), ['proof']).
% 149.67/150.15  # SZS output end CNFRefutation
% 149.67/150.15  # Proof object total steps             : 70
% 149.67/150.15  # Proof object clause steps            : 53
% 149.67/150.15  # Proof object formula steps           : 17
% 149.67/150.15  # Proof object conjectures             : 4
% 149.67/150.15  # Proof object clause conjectures      : 2
% 149.67/150.15  # Proof object formula conjectures     : 2
% 149.67/150.15  # Proof object initial clauses used    : 13
% 149.67/150.15  # Proof object initial formulas used   : 8
% 149.67/150.15  # Proof object generating inferences   : 40
% 149.67/150.15  # Proof object simplifying inferences  : 27
% 149.67/150.15  # Training examples: 0 positive, 0 negative
% 149.67/150.15  # Parsed axioms                        : 14
% 149.67/150.15  # Removed by relevancy pruning/SinE    : 0
% 149.67/150.15  # Initial clauses                      : 19
% 149.67/150.15  # Removed in clause preprocessing      : 6
% 149.67/150.15  # Initial clauses in saturation        : 13
% 149.67/150.15  # Processed clauses                    : 3266
% 149.67/150.15  # ...of these trivial                  : 513
% 149.67/150.15  # ...subsumed                          : 1673
% 149.67/150.15  # ...remaining for further processing  : 1080
% 149.67/150.15  # Other redundant clauses eliminated   : 0
% 149.67/150.15  # Clauses deleted for lack of memory   : 0
% 149.67/150.15  # Backward-subsumed                    : 24
% 149.67/150.15  # Backward-rewritten                   : 122
% 149.67/150.15  # Generated clauses                    : 20218
% 149.67/150.15  # ...of the previous two non-trivial   : 17952
% 149.67/150.15  # Contextual simplify-reflections      : 90
% 149.67/150.15  # Paramodulations                      : 20185
% 149.67/150.15  # Factorizations                       : 0
% 149.67/150.15  # NegExts                              : 9
% 149.67/150.15  # Equation resolutions                 : 0
% 149.67/150.15  # Propositional unsat checks           : 0
% 149.67/150.15  #    Propositional check models        : 0
% 149.67/150.15  #    Propositional check unsatisfiable : 0
% 149.67/150.15  #    Propositional clauses             : 0
% 149.67/150.15  #    Propositional clauses after purity: 0
% 149.67/150.15  #    Propositional unsat core size     : 0
% 149.67/150.15  #    Propositional preprocessing time  : 0.000
% 149.67/150.15  #    Propositional encoding time       : 0.000
% 149.67/150.15  #    Propositional solver time         : 0.000
% 149.67/150.15  #    Success case prop preproc time    : 0.000
% 149.67/150.15  #    Success case prop encoding time   : 0.000
% 149.67/150.15  #    Success case prop solver time     : 0.000
% 149.67/150.15  # Current number of processed clauses  : 931
% 149.67/150.15  #    Positive orientable unit clauses  : 310
% 149.67/150.15  #    Positive unorientable unit clauses: 0
% 149.67/150.15  #    Negative unit clauses             : 1
% 149.67/150.15  #    Non-unit-clauses                  : 620
% 149.67/150.15  # Current number of unprocessed clauses: 14564
% 149.67/150.15  # ...number of literals in the above   : 37765
% 149.67/150.15  # Current number of archived formulas  : 0
% 149.67/150.15  # Current number of archived clauses   : 149
% 149.67/150.15  # Clause-clause subsumption calls (NU) : 57631
% 149.67/150.15  # Rec. Clause-clause subsumption calls : 56362
% 149.67/150.15  # Non-unit clause-clause subsumptions  : 1777
% 149.67/150.15  # Unit Clause-clause subsumption calls : 432
% 149.67/150.15  # Rewrite failures with RHS unbound    : 0
% 149.67/150.15  # BW rewrite match attempts            : 3071
% 149.67/150.15  # BW rewrite match successes           : 60
% 149.67/150.15  # Condensation attempts                : 0
% 149.67/150.15  # Condensation successes               : 0
% 149.67/150.15  # Termbank termtop insertions          : 652082
% 149.67/150.16  
% 149.67/150.16  # -------------------------------------------------
% 149.67/150.16  # User time                : 147.640 s
% 149.67/150.16  # System time              : 1.894 s
% 149.67/150.16  # Total time               : 149.534 s
% 149.67/150.16  # Maximum resident set size: 1636 pages
%------------------------------------------------------------------------------
