%------------------------------------------------------------------------------
% File     : E---3.0
% Problem  : theBenchmark.p : TPTP v0.0.0. Released v0.0.0.
% Transfm  : none
% Format   : tptp:raw
% Command  : run_E %s %d THM

% Computer : n005.cluster.edu
% Model    : x86_64 x86_64
% CPU      : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory   : 8042.1875MB
% OS       : Linux 3.10.0-693.el7.x86_64
% CPULimit : 300s
% WCLimit  : 300s
% DateTime : Mon Aug  1 10:14:12 EDT 2022

% Result   : Theorem 13.75s 2.28s
% Output   : CNFRefutation 13.75s
% Verified : 
% SZS Type : Refutation
%            Derivation depth      :   16
%            Number of leaves      :   16
% Syntax   : Number of formulae    :   69 (  26 unt;   8 typ;   0 def)
%            Number of atoms       :  141 (  12 equ;   0 cnn)
%            Maximal formula atoms :    7 (   2 avg)
%            Number of connectives :  545 (  54   ~;  61   |;   7   &; 416   @)
%                                         (   2 <=>;   5  =>;   0  <=;   0 <~>)
%            Maximal formula depth :   13 (   6 avg)
%            Number of types       :    2 (   0 usr)
%            Number of type conns  :   33 (  33   >;   0   *;   0   +;   0  <<)
%            Number of symbols     :   10 (   8 usr;   2 con; 0-3 aty)
%            Number of variables   :   77 (   4   ^  73   !;   0   ?;  77   :)

% Comments : 
%------------------------------------------------------------------------------
thf(decl_22,type,
    e: $i ).

thf(decl_23,type,
    s: $i > $i ).

thf(decl_24,type,
    d: $i > $o ).

thf(decl_25,type,
    f: $i > $i > $i ).

thf(decl_26,type,
    isIndSet: ( $i > $o ) > $o ).

thf(decl_27,type,
    p: $i > $i > $o ).

thf(decl_28,type,
    esk1_1: ( $i > $o ) > $i ).

thf(decl_29,type,
    epred1_2: $i > $i > $i > $o ).

thf(p_def,axiom,
    ( p
    = ( ^ [X3: $i,X2: $i] :
          ( ^ [X5: $i] :
            ! [X6: $i > $o] :
              ( ( isIndSet @ X6 )
             => ( X6 @ X5 ) )
          @ ( f @ X3 @ X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',p_def) ).

thf(a2,axiom,
    ! [X2: $i] :
      ( ( f @ e @ ( s @ X2 ) )
      = ( s @ ( s @ ( f @ e @ X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',a2) ).

thf(a1,axiom,
    ! [X1: $i] :
      ( ( f @ X1 @ e )
      = ( s @ e ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',a1) ).

thf(isIndSet_def,axiom,
    ( isIndSet
    = ( ^ [X4: $i > $o] :
          ( ( X4 @ e )
          & ! [X3: $i] :
              ( ( X4 @ X3 )
             => ( X4 @ ( s @ X3 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',isIndSet_def) ).

thf(a5,axiom,
    ! [X3: $i] :
      ( ( d @ X3 )
     => ( d @ ( s @ X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',a5) ).

thf(a3,axiom,
    ! [X3: $i,X2: $i] :
      ( ( f @ ( s @ X3 ) @ ( s @ X2 ) )
      = ( f @ X3 @ ( f @ ( s @ X3 ) @ X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',a3) ).

thf(a4,axiom,
    d @ e,
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',a4) ).

thf(conj_0,conjecture,
    d @ ( f @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',conj_0) ).

thf(c_0_8,plain,
    ! [X13: $i,X14: $i] :
      ( ( p @ X13 @ X14 )
    <=> ! [X6: $i > $o] :
          ( ( isIndSet @ X6 )
         => ( X6 @ ( f @ X13 @ X14 ) ) ) ),
    inference(fof_simplification,[status(thm)],[inference(fof_simplification,[status(thm)],[p_def])]) ).

thf(c_0_9,plain,
    ! [X16: $i] :
      ( ( f @ e @ ( s @ X16 ) )
      = ( s @ ( s @ ( f @ e @ X16 ) ) ) ),
    inference(variable_rename,[status(thm)],[a2]) ).

thf(c_0_10,plain,
    ! [X15: $i] :
      ( ( f @ X15 @ e )
      = ( s @ e ) ),
    inference(variable_rename,[status(thm)],[a1]) ).

thf(c_0_11,plain,
    ! [X12: $i > $o] :
      ( ( isIndSet @ X12 )
    <=> ( ( X12 @ e )
        & ! [X3: $i] :
            ( ( X12 @ X3 )
           => ( X12 @ ( s @ X3 ) ) ) ) ),
    inference(fof_simplification,[status(thm)],[inference(fof_simplification,[status(thm)],[isIndSet_def])]) ).

thf(c_0_12,plain,
    ! [X24: $i,X25: $i,X26: $i > $o,X27: $i,X28: $i] :
      ( ( ~ ( p @ X24 @ X25 )
        | ~ ( isIndSet @ X26 )
        | ( X26 @ ( f @ X24 @ X25 ) ) )
      & ( ( isIndSet @ ( epred1_2 @ X27 @ X28 ) )
        | ( p @ X27 @ X28 ) )
      & ( ~ ( epred1_2 @ X27 @ X28 @ ( f @ X27 @ X28 ) )
        | ( p @ X27 @ X28 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_8])])])])])]) ).

thf(c_0_13,plain,
    ! [X1: $i] :
      ( ( f @ e @ ( s @ X1 ) )
      = ( s @ ( s @ ( f @ e @ X1 ) ) ) ),
    inference(split_conjunct,[status(thm)],[c_0_9]) ).

thf(c_0_14,plain,
    ! [X1: $i] :
      ( ( f @ X1 @ e )
      = ( s @ e ) ),
    inference(split_conjunct,[status(thm)],[c_0_10]) ).

thf(c_0_15,plain,
    ! [X20: $i > $o,X21: $i,X22: $i > $o] :
      ( ( ( X20 @ e )
        | ~ ( isIndSet @ X20 ) )
      & ( ~ ( X20 @ X21 )
        | ( X20 @ ( s @ X21 ) )
        | ~ ( isIndSet @ X20 ) )
      & ( ( X22 @ ( esk1_1 @ X22 ) )
        | ~ ( X22 @ e )
        | ( isIndSet @ X22 ) )
      & ( ~ ( X22 @ ( s @ ( esk1_1 @ X22 ) ) )
        | ~ ( X22 @ e )
        | ( isIndSet @ X22 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])])])]) ).

thf(c_0_16,plain,
    ! [X1: $i,X2: $i] :
      ( ( p @ X1 @ X2 )
      | ~ ( epred1_2 @ X1 @ X2 @ ( f @ X1 @ X2 ) ) ),
    inference(split_conjunct,[status(thm)],[c_0_12]) ).

thf(c_0_17,plain,
    ( ( f @ e @ ( s @ e ) )
    = ( s @ ( s @ ( s @ e ) ) ) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14]) ).

thf(c_0_18,plain,
    ! [X1: $i,X4: $i > $o] :
      ( ( X4 @ ( s @ X1 ) )
      | ~ ( X4 @ X1 )
      | ~ ( isIndSet @ X4 ) ),
    inference(split_conjunct,[status(thm)],[c_0_15]) ).

thf(c_0_19,plain,
    ! [X1: $i,X2: $i] :
      ( ( isIndSet @ ( epred1_2 @ X1 @ X2 ) )
      | ( p @ X1 @ X2 ) ),
    inference(split_conjunct,[status(thm)],[c_0_12]) ).

thf(c_0_20,plain,
    ( ( p @ e @ ( s @ e ) )
    | ~ ( epred1_2 @ e @ ( s @ e ) @ ( s @ ( s @ ( s @ e ) ) ) ) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17]) ).

thf(c_0_21,plain,
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( epred1_2 @ X1 @ X2 @ ( s @ X3 ) )
      | ( p @ X1 @ X2 )
      | ~ ( epred1_2 @ X1 @ X2 @ X3 ) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19]) ).

thf(c_0_22,plain,
    ( ( p @ e @ ( s @ e ) )
    | ~ ( epred1_2 @ e @ ( s @ e ) @ ( s @ ( s @ e ) ) ) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21]) ).

thf(c_0_23,plain,
    ! [X4: $i > $o] :
      ( ( X4 @ e )
      | ~ ( isIndSet @ X4 ) ),
    inference(split_conjunct,[status(thm)],[c_0_15]) ).

thf(c_0_24,plain,
    ( ( p @ e @ ( s @ e ) )
    | ~ ( epred1_2 @ e @ ( s @ e ) @ ( s @ e ) ) ),
    inference(spm,[status(thm)],[c_0_22,c_0_21]) ).

thf(c_0_25,plain,
    ! [X1: $i,X2: $i] :
      ( ( epred1_2 @ X1 @ X2 @ e )
      | ( p @ X1 @ X2 ) ),
    inference(spm,[status(thm)],[c_0_23,c_0_19]) ).

thf(c_0_26,plain,
    ! [X1: $i,X2: $i,X4: $i > $o] :
      ( ( X4 @ ( f @ X1 @ X2 ) )
      | ~ ( p @ X1 @ X2 )
      | ~ ( isIndSet @ X4 ) ),
    inference(split_conjunct,[status(thm)],[c_0_12]) ).

thf(c_0_27,plain,
    ! [X4: $i > $o] :
      ( ( X4 @ ( esk1_1 @ X4 ) )
      | ( isIndSet @ X4 )
      | ~ ( X4 @ e ) ),
    inference(split_conjunct,[status(thm)],[c_0_15]) ).

thf(c_0_28,plain,
    ! [X1: $i] :
      ( ( p @ X1 @ e )
      | ~ ( epred1_2 @ X1 @ e @ ( s @ e ) ) ),
    inference(spm,[status(thm)],[c_0_16,c_0_14]) ).

thf(c_0_29,plain,
    p @ e @ ( s @ e ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_21]),c_0_25]) ).

thf(c_0_30,plain,
    ! [X1: $i,X4: $i > $o] :
      ( ( X4 @ ( f @ X1 @ ( esk1_1 @ ( p @ X1 ) ) ) )
      | ( isIndSet @ ( p @ X1 ) )
      | ~ ( p @ X1 @ e )
      | ~ ( isIndSet @ X4 ) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27]) ).

thf(c_0_31,plain,
    ! [X1: $i] : ( p @ X1 @ e ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_21]),c_0_25]) ).

thf(c_0_32,plain,
    ! [X4: $i > $o] :
      ( ( X4 @ ( s @ ( s @ ( s @ e ) ) ) )
      | ~ ( isIndSet @ X4 ) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_29]),c_0_17]) ).

thf(c_0_33,plain,
    ! [X19: $i] :
      ( ~ ( d @ X19 )
      | ( d @ ( s @ X19 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[a5])]) ).

thf(c_0_34,plain,
    ! [X1: $i,X4: $i > $o] :
      ( ( X4 @ ( f @ X1 @ ( esk1_1 @ ( p @ X1 ) ) ) )
      | ( isIndSet @ ( p @ X1 ) )
      | ~ ( isIndSet @ X4 ) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_30,c_0_31])]) ).

thf(c_0_35,plain,
    ! [X17: $i,X18: $i] :
      ( ( f @ ( s @ X17 ) @ ( s @ X18 ) )
      = ( f @ X17 @ ( f @ ( s @ X17 ) @ X18 ) ) ),
    inference(variable_rename,[status(thm)],[a3]) ).

thf(c_0_36,plain,
    ! [X1: $i,X4: $i > $o] :
      ( ( X4 @ ( f @ X1 @ ( s @ ( s @ ( s @ e ) ) ) ) )
      | ~ ( isIndSet @ ( p @ X1 ) )
      | ~ ( isIndSet @ X4 ) ),
    inference(spm,[status(thm)],[c_0_26,c_0_32]) ).

thf(c_0_37,plain,
    ! [X4: $i > $o] :
      ( ( isIndSet @ X4 )
      | ~ ( X4 @ ( s @ ( esk1_1 @ X4 ) ) )
      | ~ ( X4 @ e ) ),
    inference(split_conjunct,[status(thm)],[c_0_15]) ).

thf(c_0_38,plain,
    ! [X1: $i] :
      ( ( d @ ( s @ X1 ) )
      | ~ ( d @ X1 ) ),
    inference(split_conjunct,[status(thm)],[c_0_33]) ).

thf(c_0_39,plain,
    d @ e,
    inference(split_conjunct,[status(thm)],[a4]) ).

thf(c_0_40,plain,
    ! [X1: $i,X2: $i,X4: $i > $o] :
      ( ( X4 @ ( f @ X1 @ ( f @ X2 @ ( esk1_1 @ ( p @ X2 ) ) ) ) )
      | ( isIndSet @ ( p @ X2 ) )
      | ~ ( isIndSet @ ( p @ X1 ) )
      | ~ ( isIndSet @ X4 ) ),
    inference(spm,[status(thm)],[c_0_26,c_0_34]) ).

thf(c_0_41,plain,
    ! [X1: $i,X2: $i] :
      ( ( f @ ( s @ X1 ) @ ( s @ X2 ) )
      = ( f @ X1 @ ( f @ ( s @ X1 ) @ X2 ) ) ),
    inference(split_conjunct,[status(thm)],[c_0_35]) ).

thf(c_0_42,negated_conjecture,
    ~ ( d @ ( f @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) ) ),
    inference(fof_simplification,[status(thm)],[inference(assume_negation,[status(cth)],[conj_0])]) ).

thf(c_0_43,plain,
    ! [X1: $i,X2: $i,X4: $i > $o] :
      ( ( X4 @ ( f @ X1 @ ( f @ X2 @ ( s @ ( s @ ( s @ e ) ) ) ) ) )
      | ~ ( isIndSet @ ( p @ X2 ) )
      | ~ ( isIndSet @ ( p @ X1 ) )
      | ~ ( isIndSet @ X4 ) ),
    inference(spm,[status(thm)],[c_0_26,c_0_36]) ).

thf(c_0_44,plain,
    ( ( isIndSet @ d )
    | ~ ( d @ ( esk1_1 @ d ) ) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39])]) ).

thf(c_0_45,plain,
    ! [X1: $i,X4: $i > $o] :
      ( ( X4 @ ( f @ ( s @ X1 ) @ ( s @ ( esk1_1 @ ( p @ ( s @ X1 ) ) ) ) ) )
      | ( isIndSet @ ( p @ ( s @ X1 ) ) )
      | ~ ( isIndSet @ ( p @ X1 ) )
      | ~ ( isIndSet @ X4 ) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41]) ).

thf(c_0_46,negated_conjecture,
    ~ ( d @ ( f @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) ) ),
    inference(split_conjunct,[status(thm)],[c_0_42]) ).

thf(c_0_47,plain,
    ! [X1: $i,X4: $i > $o] :
      ( ( X4 @ ( f @ ( s @ X1 ) @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) ) )
      | ~ ( isIndSet @ ( p @ ( s @ X1 ) ) )
      | ~ ( isIndSet @ ( p @ X1 ) )
      | ~ ( isIndSet @ X4 ) ),
    inference(spm,[status(thm)],[c_0_43,c_0_41]) ).

thf(c_0_48,plain,
    isIndSet @ d,
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_27]),c_0_39])]) ).

thf(c_0_49,plain,
    ! [X1: $i] :
      ( ( p @ ( s @ X1 ) @ ( s @ ( esk1_1 @ ( p @ ( s @ X1 ) ) ) ) )
      | ( isIndSet @ ( p @ ( s @ X1 ) ) )
      | ~ ( isIndSet @ ( p @ X1 ) ) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_45]),c_0_19]) ).

thf(c_0_50,plain,
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( epred1_2 @ X1 @ X2 @ ( f @ e @ ( s @ X3 ) ) )
      | ( p @ X1 @ X2 )
      | ~ ( epred1_2 @ X1 @ X2 @ ( s @ ( f @ e @ X3 ) ) ) ),
    inference(spm,[status(thm)],[c_0_21,c_0_13]) ).

thf(c_0_51,negated_conjecture,
    ( ~ ( isIndSet @ ( p @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) ) )
    | ~ ( isIndSet @ ( p @ ( s @ ( s @ ( s @ e ) ) ) ) ) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48])]) ).

thf(c_0_52,plain,
    ! [X1: $i] :
      ( ( isIndSet @ ( p @ ( s @ X1 ) ) )
      | ~ ( isIndSet @ ( p @ X1 ) ) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_49]),c_0_31])]) ).

thf(c_0_53,plain,
    ! [X1: $i] :
      ( ( p @ e @ ( s @ X1 ) )
      | ~ ( epred1_2 @ e @ ( s @ X1 ) @ ( s @ ( f @ e @ X1 ) ) ) ),
    inference(spm,[status(thm)],[c_0_16,c_0_50]) ).

thf(c_0_54,negated_conjecture,
    ~ ( isIndSet @ ( p @ ( s @ ( s @ ( s @ e ) ) ) ) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52]) ).

thf(c_0_55,plain,
    ! [X1: $i] :
      ( ( p @ e @ ( s @ X1 ) )
      | ~ ( epred1_2 @ e @ ( s @ X1 ) @ ( f @ e @ X1 ) ) ),
    inference(spm,[status(thm)],[c_0_53,c_0_21]) ).

thf(c_0_56,negated_conjecture,
    ~ ( isIndSet @ ( p @ ( s @ ( s @ e ) ) ) ),
    inference(spm,[status(thm)],[c_0_54,c_0_52]) ).

thf(c_0_57,plain,
    ( ( p @ e @ ( s @ ( esk1_1 @ ( p @ e ) ) ) )
    | ( isIndSet @ ( p @ e ) ) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_34]),c_0_19]) ).

thf(c_0_58,negated_conjecture,
    ~ ( isIndSet @ ( p @ ( s @ e ) ) ),
    inference(spm,[status(thm)],[c_0_56,c_0_52]) ).

thf(c_0_59,plain,
    isIndSet @ ( p @ e ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_57]),c_0_31])]) ).

thf(c_0_60,negated_conjecture,
    $false,
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_52]),c_0_59])]),
    [proof] ).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.16  % Problem    : theBenchmark.p : TPTP v0.0.0. Released v0.0.0.
% 0.12/0.17  % Command    : run_E %s %d THM
% 0.14/0.38  % Computer : n005.cluster.edu
% 0.14/0.38  % Model    : x86_64 x86_64
% 0.14/0.38  % CPU      : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.38  % Memory   : 8042.1875MB
% 0.14/0.38  % OS       : Linux 3.10.0-693.el7.x86_64
% 0.14/0.38  % CPULimit   : 300
% 0.14/0.38  % WCLimit    : 300
% 0.14/0.38  % DateTime   : Mon Aug  1 10:26:50 EDT 2022
% 0.14/0.38  % CPUTime    : 
% 0.20/0.53  Running higher-order on 8 cores theorem proving
% 0.20/0.53  Running: /export/starexec/sandbox2/solver/bin/eprover-ho --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule=8 --cpu-limit=300 /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.32/0.54  # Version: 3.0pre003-ho
% 13.75/2.28  # partial match(1): HSMSSMSSSSSNFFN
% 13.75/2.28  # Preprocessing class: HSMSSMSSSSSNHFN.
% 13.75/2.28  # Scheduled 4 strats onto 8 cores with 300 seconds (2400 total)
% 13.75/2.28  # Starting new_ho_10 with 1500s (5) cores
% 13.75/2.28  # Starting new_bool_1 with 300s (1) cores
% 13.75/2.28  # Starting full_lambda_5 with 300s (1) cores
% 13.75/2.28  # Starting new_ho_10_unif with 300s (1) cores
% 13.75/2.28  # new_ho_10 with pid 26097 completed with status 0
% 13.75/2.28  # Result found by new_ho_10
% 13.75/2.28  # partial match(1): HSMSSMSSSSSNFFN
% 13.75/2.28  # Preprocessing class: HSMSSMSSSSSNHFN.
% 13.75/2.28  # Scheduled 4 strats onto 8 cores with 300 seconds (2400 total)
% 13.75/2.28  # Starting new_ho_10 with 1500s (5) cores
% 13.75/2.28  # No SInE strategy applied
% 13.75/2.28  # Search class: HGUSS-FFSF21-MHFFFSBN
% 13.75/2.28  # partial match(2): HGUSS-FFSF11-MHHFFSBN
% 13.75/2.28  # Scheduled 6 strats onto 5 cores with 1500 seconds (1500 total)
% 13.75/2.28  # Starting new_ho_10_unif with 811s (1) cores
% 13.75/2.28  # Starting new_ho_10 with 151s (1) cores
% 13.75/2.28  # Starting lpo8_s with 136s (1) cores
% 13.75/2.28  # Starting sh5l with 136s (1) cores
% 13.75/2.28  # Starting sh2lt with 136s (1) cores
% 13.75/2.28  # new_ho_10 with pid 26104 completed with status 0
% 13.75/2.28  # Result found by new_ho_10
% 13.75/2.28  # partial match(1): HSMSSMSSSSSNFFN
% 13.75/2.28  # Preprocessing class: HSMSSMSSSSSNHFN.
% 13.75/2.28  # Scheduled 4 strats onto 8 cores with 300 seconds (2400 total)
% 13.75/2.28  # Starting new_ho_10 with 1500s (5) cores
% 13.75/2.28  # No SInE strategy applied
% 13.75/2.28  # Search class: HGUSS-FFSF21-MHFFFSBN
% 13.75/2.28  # partial match(2): HGUSS-FFSF11-MHHFFSBN
% 13.75/2.28  # Scheduled 6 strats onto 5 cores with 1500 seconds (1500 total)
% 13.75/2.28  # Starting new_ho_10_unif with 811s (1) cores
% 13.75/2.28  # Starting new_ho_10 with 151s (1) cores
% 13.75/2.28  # Preprocessing time       : 0.001 s
% 13.75/2.28  # Presaturation interreduction done
% 13.75/2.28  
% 13.75/2.28  # Proof found!
% 13.75/2.28  # SZS status Theorem
% 13.75/2.28  # SZS output start CNFRefutation
% See solution above
% 13.75/2.28  # Parsed axioms                        : 14
% 13.75/2.28  # Removed by relevancy pruning/SinE    : 0
% 13.75/2.28  # Initial clauses                      : 19
% 13.75/2.28  # Removed in clause preprocessing      : 6
% 13.75/2.28  # Initial clauses in saturation        : 13
% 13.75/2.28  # Processed clauses                    : 4451
% 13.75/2.28  # ...of these trivial                  : 952
% 13.75/2.28  # ...subsumed                          : 2217
% 13.75/2.28  # ...remaining for further processing  : 1282
% 13.75/2.28  # Other redundant clauses eliminated   : 0
% 13.75/2.28  # Clauses deleted for lack of memory   : 0
% 13.75/2.28  # Backward-subsumed                    : 77
% 13.75/2.28  # Backward-rewritten                   : 139
% 13.75/2.28  # Generated clauses                    : 54638
% 13.75/2.28  # ...of the previous two non-redundant : 49054
% 13.75/2.28  # ...aggressively subsumed             : 0
% 13.75/2.28  # Contextual simplify-reflections      : 95
% 13.75/2.28  # Paramodulations                      : 54638
% 13.75/2.28  # Factorizations                       : 0
% 13.75/2.28  # NegExts                              : 0
% 13.75/2.28  # Equation resolutions                 : 0
% 13.75/2.28  # Propositional unsat checks           : 0
% 13.75/2.28  #    Propositional check models        : 0
% 13.75/2.28  #    Propositional check unsatisfiable : 0
% 13.75/2.28  #    Propositional clauses             : 0
% 13.75/2.28  #    Propositional clauses after purity: 0
% 13.75/2.28  #    Propositional unsat core size     : 0
% 13.75/2.28  #    Propositional preprocessing time  : 0.000
% 13.75/2.28  #    Propositional encoding time       : 0.000
% 13.75/2.28  #    Propositional solver time         : 0.000
% 13.75/2.28  #    Success case prop preproc time    : 0.000
% 13.75/2.28  #    Success case prop encoding time   : 0.000
% 13.75/2.28  #    Success case prop solver time     : 0.000
% 13.75/2.28  # Current number of processed clauses  : 1053
% 13.75/2.28  #    Positive orientable unit clauses  : 443
% 13.75/2.28  #    Positive unorientable unit clauses: 10
% 13.75/2.28  #    Negative unit clauses             : 4
% 13.75/2.28  #    Non-unit-clauses                  : 596
% 13.75/2.28  # Current number of unprocessed clauses: 44213
% 13.75/2.28  # ...number of literals in the above   : 85482
% 13.75/2.28  # Current number of archived formulas  : 0
% 13.75/2.28  # Current number of archived clauses   : 229
% 13.75/2.28  # Clause-clause subsumption calls (NU) : 180168
% 13.75/2.28  # Rec. Clause-clause subsumption calls : 178831
% 13.75/2.28  # Non-unit clause-clause subsumptions  : 2351
% 13.75/2.28  # Unit Clause-clause subsumption calls : 4024
% 13.75/2.28  # Rewrite failures with RHS unbound    : 0
% 13.75/2.28  # BW rewrite match attempts            : 9295
% 13.75/2.28  # BW rewrite match successes           : 149
% 13.75/2.28  # Condensation attempts                : 4451
% 13.75/2.28  # Condensation successes               : 0
% 13.75/2.28  # Termbank termtop insertions          : 4271812
% 13.75/2.28  
% 13.75/2.28  # -------------------------------------------------
% 13.75/2.28  # User time                : 1.673 s
% 13.75/2.28  # System time              : 0.047 s
% 13.75/2.28  # Total time               : 1.720 s
% 13.75/2.28  # Maximum resident set size: 1848 pages
% 13.75/2.28  
% 13.75/2.28  # -------------------------------------------------
% 13.75/2.28  # User time                : 8.355 s
% 13.75/2.28  # System time              : 0.256 s
% 13.75/2.28  # Total time               : 8.611 s
% 13.75/2.28  # Maximum resident set size: 1724 pages
%------------------------------------------------------------------------------
