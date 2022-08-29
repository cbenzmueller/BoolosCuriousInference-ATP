%------------------------------------------------------------------------------
% File     : E---3.0
% Problem  : theBenchmark.p : TPTP v0.0.0. Released v0.0.0.
% Transfm  : none
% Format   : tptp:raw
% Command  : run_E %s %d THM

% Computer : n012.cluster.edu
% Model    : x86_64 x86_64
% CPU      : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory   : 8042.1875MB
% OS       : Linux 3.10.0-693.el7.x86_64
% CPULimit : 300s
% WCLimit  : 300s
% DateTime : Mon Aug  1 10:14:12 EDT 2022

% Result   : Theorem 0.19s 0.74s
% Output   : CNFRefutation 0.19s
% Verified : 
% SZS Type : Refutation
%            Derivation depth      :   20
%            Number of leaves      :   21
% Syntax   : Number of formulae    :   87 (  29 unt;  13 typ;   0 def)
%            Number of atoms       :  364 (  12 equ;   0 cnn)
%            Maximal formula atoms :  207 (   4 avg)
%            Number of connectives : 1569 ( 245   ~; 331   |; 146   &; 837   @)
%                                         (   2 <=>;   8  =>;   0  <=;   0 <~>)
%            Maximal formula depth :   67 (   7 avg)
%            Number of types       :    2 (   0 usr)
%            Number of type conns  :   52 (  52   >;   0   *;   0   +;   0  <<)
%            Number of symbols     :   16 (  13 usr;   5 con; 0-3 aty)
%            Number of variables   :  101 (   4   ^  95   !;   2   ?; 101   :)

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
    epred1_1: ( $i > $o ) > $o ).

thf(decl_27,type,
    epred2_0: $i > $i > $o ).

thf(decl_28,type,
    epred3_2: $i > $i > $i > $o ).

thf(decl_29,type,
    esk1_1: ( $i > $o ) > $i ).

thf(decl_30,type,
    esk2_1: ( $i > $o ) > $i ).

thf(decl_31,type,
    esk3_1: ( $i > $o ) > $i ).

thf(decl_32,type,
    esk4_1: ( $i > $o ) > $i ).

thf(decl_33,type,
    epred4_0: $o ).

thf(decl_34,type,
    epred5_0: $o ).

thf(p_def,axiom,
    ? [X4: $i > $i > $o] :
      ( X4
      = ( ^ [X3: $i,X2: $i] :
            ( ^ [X5: $i] :
              ! [X6: $i > $o] :
                ( ( ^ [X7: $i > $o] :
                      ( ( X7 @ e )
                      & ! [X3: $i] :
                          ( ( X7 @ X3 )
                         => ( X7 @ ( s @ X3 ) ) ) )
                  @ X6 )
               => ( X6 @ X5 ) )
            @ ( f @ X3 @ X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',p_def) ).

thf(a3,axiom,
    ! [X3: $i,X2: $i] :
      ( ( f @ ( s @ X3 ) @ ( s @ X2 ) )
      = ( f @ X3 @ ( f @ ( s @ X3 ) @ X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',a3) ).

thf(a1,axiom,
    ! [X1: $i] :
      ( ( f @ X1 @ e )
      = ( s @ e ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',a1) ).

thf(a2,axiom,
    ! [X2: $i] :
      ( ( f @ e @ ( s @ X2 ) )
      = ( s @ ( s @ ( f @ e @ X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',a2) ).

thf(conj_0,conjecture,
    d @ ( f @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',conj_0) ).

thf(a5,axiom,
    ! [X3: $i] :
      ( ( d @ X3 )
     => ( d @ ( s @ X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',a5) ).

thf(a4,axiom,
    d @ e,
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',a4) ).

thf(c_0_7,plain,
    ! [X6: $i > $o] :
      ( ( epred1_1 @ X6 )
    <=> ( ( ~ ( X6 @ e )
          | ( ( ~ ! [X14: $i] :
                    ( ( X6 @ X14 )
                   => ( X6 @ ( s @ X14 ) ) )
              | ( $true
                & $true ) )
            & ( ! [X14: $i] :
                  ( ( X6 @ X14 )
                 => ( X6 @ ( s @ X14 ) ) )
              | ( $true
                & $false ) ) ) )
        & ( ( X6 @ e )
          | ( ( ~ ! [X14: $i] :
                    ( ( X6 @ X14 )
                   => ( X6 @ ( s @ X14 ) ) )
              | ( $false
                & $true ) )
            & ( ! [X14: $i] :
                  ( ( X6 @ X14 )
                 => ( X6 @ ( s @ X14 ) ) )
              | ( $false
                & $false ) ) ) ) ) ),
    introduced(definition) ).

thf(c_0_8,plain,
    ! [X26: $i > $o,X28: $i,X30: $i,X31: $i > $o,X32: $i,X34: $i] :
      ( ( ( X26 @ ( esk1_1 @ X26 ) )
        | ( $true
          & $true )
        | ~ ( X26 @ e )
        | ~ ( epred1_1 @ X26 ) )
      & ( ~ ( X26 @ ( s @ ( esk1_1 @ X26 ) ) )
        | ( $true
          & $true )
        | ~ ( X26 @ e )
        | ~ ( epred1_1 @ X26 ) )
      & ( ~ ( X26 @ X28 )
        | ( X26 @ ( s @ X28 ) )
        | ( $true
          & $false )
        | ~ ( X26 @ e )
        | ~ ( epred1_1 @ X26 ) )
      & ( ( X26 @ ( esk2_1 @ X26 ) )
        | ( $false
          & $true )
        | ( X26 @ e )
        | ~ ( epred1_1 @ X26 ) )
      & ( ~ ( X26 @ ( s @ ( esk2_1 @ X26 ) ) )
        | ( $false
          & $true )
        | ( X26 @ e )
        | ~ ( epred1_1 @ X26 ) )
      & ( ~ ( X26 @ X30 )
        | ( X26 @ ( s @ X30 ) )
        | ( $false
          & $false )
        | ( X26 @ e )
        | ~ ( epred1_1 @ X26 ) )
      & ( ~ ( X31 @ e )
        | ( X31 @ e )
        | ( epred1_1 @ X31 ) )
      & ( ( X31 @ ( esk4_1 @ X31 ) )
        | ~ ( X31 @ X34 )
        | ( X31 @ ( s @ X34 ) )
        | ( X31 @ e )
        | ( epred1_1 @ X31 ) )
      & ( ~ ( X31 @ ( s @ ( esk4_1 @ X31 ) ) )
        | ~ ( X31 @ X34 )
        | ( X31 @ ( s @ X34 ) )
        | ( X31 @ e )
        | ( epred1_1 @ X31 ) )
      & ( ~ ( $false
            & $false )
        | ~ ( X31 @ X34 )
        | ( X31 @ ( s @ X34 ) )
        | ( X31 @ e )
        | ( epred1_1 @ X31 ) )
      & ( ( X31 @ ( esk4_1 @ X31 ) )
        | ~ ( $false
            & $true )
        | ( X31 @ e )
        | ( epred1_1 @ X31 ) )
      & ( ~ ( X31 @ ( s @ ( esk4_1 @ X31 ) ) )
        | ~ ( $false
            & $true )
        | ( X31 @ e )
        | ( epred1_1 @ X31 ) )
      & ( ~ ( $false
            & $false )
        | ~ ( $false
            & $true )
        | ( X31 @ e )
        | ( epred1_1 @ X31 ) )
      & ( ~ ( X31 @ e )
        | ( X31 @ ( esk3_1 @ X31 ) )
        | ~ ( X31 @ X32 )
        | ( X31 @ ( s @ X32 ) )
        | ( epred1_1 @ X31 ) )
      & ( ( X31 @ ( esk4_1 @ X31 ) )
        | ~ ( X31 @ X34 )
        | ( X31 @ ( s @ X34 ) )
        | ( X31 @ ( esk3_1 @ X31 ) )
        | ~ ( X31 @ X32 )
        | ( X31 @ ( s @ X32 ) )
        | ( epred1_1 @ X31 ) )
      & ( ~ ( X31 @ ( s @ ( esk4_1 @ X31 ) ) )
        | ~ ( X31 @ X34 )
        | ( X31 @ ( s @ X34 ) )
        | ( X31 @ ( esk3_1 @ X31 ) )
        | ~ ( X31 @ X32 )
        | ( X31 @ ( s @ X32 ) )
        | ( epred1_1 @ X31 ) )
      & ( ~ ( $false
            & $false )
        | ~ ( X31 @ X34 )
        | ( X31 @ ( s @ X34 ) )
        | ( X31 @ ( esk3_1 @ X31 ) )
        | ~ ( X31 @ X32 )
        | ( X31 @ ( s @ X32 ) )
        | ( epred1_1 @ X31 ) )
      & ( ( X31 @ ( esk4_1 @ X31 ) )
        | ~ ( $false
            & $true )
        | ( X31 @ ( esk3_1 @ X31 ) )
        | ~ ( X31 @ X32 )
        | ( X31 @ ( s @ X32 ) )
        | ( epred1_1 @ X31 ) )
      & ( ~ ( X31 @ ( s @ ( esk4_1 @ X31 ) ) )
        | ~ ( $false
            & $true )
        | ( X31 @ ( esk3_1 @ X31 ) )
        | ~ ( X31 @ X32 )
        | ( X31 @ ( s @ X32 ) )
        | ( epred1_1 @ X31 ) )
      & ( ~ ( $false
            & $false )
        | ~ ( $false
            & $true )
        | ( X31 @ ( esk3_1 @ X31 ) )
        | ~ ( X31 @ X32 )
        | ( X31 @ ( s @ X32 ) )
        | ( epred1_1 @ X31 ) )
      & ( ~ ( X31 @ e )
        | ~ ( X31 @ ( s @ ( esk3_1 @ X31 ) ) )
        | ~ ( X31 @ X32 )
        | ( X31 @ ( s @ X32 ) )
        | ( epred1_1 @ X31 ) )
      & ( ( X31 @ ( esk4_1 @ X31 ) )
        | ~ ( X31 @ X34 )
        | ( X31 @ ( s @ X34 ) )
        | ~ ( X31 @ ( s @ ( esk3_1 @ X31 ) ) )
        | ~ ( X31 @ X32 )
        | ( X31 @ ( s @ X32 ) )
        | ( epred1_1 @ X31 ) )
      & ( ~ ( X31 @ ( s @ ( esk4_1 @ X31 ) ) )
        | ~ ( X31 @ X34 )
        | ( X31 @ ( s @ X34 ) )
        | ~ ( X31 @ ( s @ ( esk3_1 @ X31 ) ) )
        | ~ ( X31 @ X32 )
        | ( X31 @ ( s @ X32 ) )
        | ( epred1_1 @ X31 ) )
      & ( ~ ( $false
            & $false )
        | ~ ( X31 @ X34 )
        | ( X31 @ ( s @ X34 ) )
        | ~ ( X31 @ ( s @ ( esk3_1 @ X31 ) ) )
        | ~ ( X31 @ X32 )
        | ( X31 @ ( s @ X32 ) )
        | ( epred1_1 @ X31 ) )
      & ( ( X31 @ ( esk4_1 @ X31 ) )
        | ~ ( $false
            & $true )
        | ~ ( X31 @ ( s @ ( esk3_1 @ X31 ) ) )
        | ~ ( X31 @ X32 )
        | ( X31 @ ( s @ X32 ) )
        | ( epred1_1 @ X31 ) )
      & ( ~ ( X31 @ ( s @ ( esk4_1 @ X31 ) ) )
        | ~ ( $false
            & $true )
        | ~ ( X31 @ ( s @ ( esk3_1 @ X31 ) ) )
        | ~ ( X31 @ X32 )
        | ( X31 @ ( s @ X32 ) )
        | ( epred1_1 @ X31 ) )
      & ( ~ ( $false
            & $false )
        | ~ ( $false
            & $true )
        | ~ ( X31 @ ( s @ ( esk3_1 @ X31 ) ) )
        | ~ ( X31 @ X32 )
        | ( X31 @ ( s @ X32 ) )
        | ( epred1_1 @ X31 ) )
      & ( ~ ( X31 @ e )
        | ~ ( $true
            & $false )
        | ~ ( X31 @ X32 )
        | ( X31 @ ( s @ X32 ) )
        | ( epred1_1 @ X31 ) )
      & ( ( X31 @ ( esk4_1 @ X31 ) )
        | ~ ( X31 @ X34 )
        | ( X31 @ ( s @ X34 ) )
        | ~ ( $true
            & $false )
        | ~ ( X31 @ X32 )
        | ( X31 @ ( s @ X32 ) )
        | ( epred1_1 @ X31 ) )
      & ( ~ ( X31 @ ( s @ ( esk4_1 @ X31 ) ) )
        | ~ ( X31 @ X34 )
        | ( X31 @ ( s @ X34 ) )
        | ~ ( $true
            & $false )
        | ~ ( X31 @ X32 )
        | ( X31 @ ( s @ X32 ) )
        | ( epred1_1 @ X31 ) )
      & ( ~ ( $false
            & $false )
        | ~ ( X31 @ X34 )
        | ( X31 @ ( s @ X34 ) )
        | ~ ( $true
            & $false )
        | ~ ( X31 @ X32 )
        | ( X31 @ ( s @ X32 ) )
        | ( epred1_1 @ X31 ) )
      & ( ( X31 @ ( esk4_1 @ X31 ) )
        | ~ ( $false
            & $true )
        | ~ ( $true
            & $false )
        | ~ ( X31 @ X32 )
        | ( X31 @ ( s @ X32 ) )
        | ( epred1_1 @ X31 ) )
      & ( ~ ( X31 @ ( s @ ( esk4_1 @ X31 ) ) )
        | ~ ( $false
            & $true )
        | ~ ( $true
            & $false )
        | ~ ( X31 @ X32 )
        | ( X31 @ ( s @ X32 ) )
        | ( epred1_1 @ X31 ) )
      & ( ~ ( $false
            & $false )
        | ~ ( $false
            & $true )
        | ~ ( $true
            & $false )
        | ~ ( X31 @ X32 )
        | ( X31 @ ( s @ X32 ) )
        | ( epred1_1 @ X31 ) )
      & ( ~ ( X31 @ e )
        | ( X31 @ ( esk3_1 @ X31 ) )
        | ~ ( $true
            & $true )
        | ( epred1_1 @ X31 ) )
      & ( ( X31 @ ( esk4_1 @ X31 ) )
        | ~ ( X31 @ X34 )
        | ( X31 @ ( s @ X34 ) )
        | ( X31 @ ( esk3_1 @ X31 ) )
        | ~ ( $true
            & $true )
        | ( epred1_1 @ X31 ) )
      & ( ~ ( X31 @ ( s @ ( esk4_1 @ X31 ) ) )
        | ~ ( X31 @ X34 )
        | ( X31 @ ( s @ X34 ) )
        | ( X31 @ ( esk3_1 @ X31 ) )
        | ~ ( $true
            & $true )
        | ( epred1_1 @ X31 ) )
      & ( ~ ( $false
            & $false )
        | ~ ( X31 @ X34 )
        | ( X31 @ ( s @ X34 ) )
        | ( X31 @ ( esk3_1 @ X31 ) )
        | ~ ( $true
            & $true )
        | ( epred1_1 @ X31 ) )
      & ( ( X31 @ ( esk4_1 @ X31 ) )
        | ~ ( $false
            & $true )
        | ( X31 @ ( esk3_1 @ X31 ) )
        | ~ ( $true
            & $true )
        | ( epred1_1 @ X31 ) )
      & ( ~ ( X31 @ ( s @ ( esk4_1 @ X31 ) ) )
        | ~ ( $false
            & $true )
        | ( X31 @ ( esk3_1 @ X31 ) )
        | ~ ( $true
            & $true )
        | ( epred1_1 @ X31 ) )
      & ( ~ ( $false
            & $false )
        | ~ ( $false
            & $true )
        | ( X31 @ ( esk3_1 @ X31 ) )
        | ~ ( $true
            & $true )
        | ( epred1_1 @ X31 ) )
      & ( ~ ( X31 @ e )
        | ~ ( X31 @ ( s @ ( esk3_1 @ X31 ) ) )
        | ~ ( $true
            & $true )
        | ( epred1_1 @ X31 ) )
      & ( ( X31 @ ( esk4_1 @ X31 ) )
        | ~ ( X31 @ X34 )
        | ( X31 @ ( s @ X34 ) )
        | ~ ( X31 @ ( s @ ( esk3_1 @ X31 ) ) )
        | ~ ( $true
            & $true )
        | ( epred1_1 @ X31 ) )
      & ( ~ ( X31 @ ( s @ ( esk4_1 @ X31 ) ) )
        | ~ ( X31 @ X34 )
        | ( X31 @ ( s @ X34 ) )
        | ~ ( X31 @ ( s @ ( esk3_1 @ X31 ) ) )
        | ~ ( $true
            & $true )
        | ( epred1_1 @ X31 ) )
      & ( ~ ( $false
            & $false )
        | ~ ( X31 @ X34 )
        | ( X31 @ ( s @ X34 ) )
        | ~ ( X31 @ ( s @ ( esk3_1 @ X31 ) ) )
        | ~ ( $true
            & $true )
        | ( epred1_1 @ X31 ) )
      & ( ( X31 @ ( esk4_1 @ X31 ) )
        | ~ ( $false
            & $true )
        | ~ ( X31 @ ( s @ ( esk3_1 @ X31 ) ) )
        | ~ ( $true
            & $true )
        | ( epred1_1 @ X31 ) )
      & ( ~ ( X31 @ ( s @ ( esk4_1 @ X31 ) ) )
        | ~ ( $false
            & $true )
        | ~ ( X31 @ ( s @ ( esk3_1 @ X31 ) ) )
        | ~ ( $true
            & $true )
        | ( epred1_1 @ X31 ) )
      & ( ~ ( $false
            & $false )
        | ~ ( $false
            & $true )
        | ~ ( X31 @ ( s @ ( esk3_1 @ X31 ) ) )
        | ~ ( $true
            & $true )
        | ( epred1_1 @ X31 ) )
      & ( ~ ( X31 @ e )
        | ~ ( $true
            & $false )
        | ~ ( $true
            & $true )
        | ( epred1_1 @ X31 ) )
      & ( ( X31 @ ( esk4_1 @ X31 ) )
        | ~ ( X31 @ X34 )
        | ( X31 @ ( s @ X34 ) )
        | ~ ( $true
            & $false )
        | ~ ( $true
            & $true )
        | ( epred1_1 @ X31 ) )
      & ( ~ ( X31 @ ( s @ ( esk4_1 @ X31 ) ) )
        | ~ ( X31 @ X34 )
        | ( X31 @ ( s @ X34 ) )
        | ~ ( $true
            & $false )
        | ~ ( $true
            & $true )
        | ( epred1_1 @ X31 ) )
      & ( ~ ( $false
            & $false )
        | ~ ( X31 @ X34 )
        | ( X31 @ ( s @ X34 ) )
        | ~ ( $true
            & $false )
        | ~ ( $true
            & $true )
        | ( epred1_1 @ X31 ) )
      & ( ( X31 @ ( esk4_1 @ X31 ) )
        | ~ ( $false
            & $true )
        | ~ ( $true
            & $false )
        | ~ ( $true
            & $true )
        | ( epred1_1 @ X31 ) )
      & ( ~ ( X31 @ ( s @ ( esk4_1 @ X31 ) ) )
        | ~ ( $false
            & $true )
        | ~ ( $true
            & $false )
        | ~ ( $true
            & $true )
        | ( epred1_1 @ X31 ) )
      & ( ~ ( $false
            & $false )
        | ~ ( $false
            & $true )
        | ~ ( $true
            & $false )
        | ~ ( $true
            & $true )
        | ( epred1_1 @ X31 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])])])]) ).

thf(c_0_9,plain,
    ! [X1: $i,X6: $i > $o] :
      ( ( X6 @ ( s @ X1 ) )
      | ( $true
        & ~ $true )
      | ~ ( X6 @ X1 )
      | ~ ( X6 @ e )
      | ~ ( epred1_1 @ X6 ) ),
    inference(split_conjunct,[status(thm)],[c_0_8]) ).

thf(c_0_10,plain,
    ! [X6: $i > $o] :
      ( ( ~ $true
        & $true )
      | ( X6 @ e )
      | ~ ( X6 @ ( s @ ( esk2_1 @ X6 ) ) )
      | ~ ( epred1_1 @ X6 ) ),
    inference(split_conjunct,[status(thm)],[c_0_8]) ).

thf(c_0_11,plain,
    ! [X1: $i,X6: $i > $o] :
      ( ( X6 @ ( s @ X1 ) )
      | ( ~ $true
        & ~ $true )
      | ( X6 @ e )
      | ~ ( X6 @ X1 )
      | ~ ( epred1_1 @ X6 ) ),
    inference(split_conjunct,[status(thm)],[c_0_8]) ).

thf(c_0_12,plain,
    ! [X6: $i > $o,X1: $i] :
      ( ( X6 @ ( s @ X1 ) )
      | ~ ( epred1_1 @ X6 )
      | ~ ( X6 @ e )
      | ~ ( X6 @ X1 ) ),
    inference(cn,[status(thm)],[inference(cn,[status(thm)],[c_0_9])]) ).

thf(c_0_13,plain,
    ? [X4: $i > $i > $o] :
    ! [X14: $i,X15: $i] :
      ( ( X4 @ X14 @ X15 )
    <=> ! [X6: $i > $o] :
          ( ( epred1_1 @ X6 )
         => ( X6 @ ( f @ X14 @ X15 ) ) ) ),
    inference(apply_def,[status(thm)],[inference(fool_unroll,[status(thm)],[inference(fof_simplification,[status(thm)],[inference(fof_simplification,[status(thm)],[p_def])])]),c_0_7]) ).

thf(c_0_14,plain,
    ! [X6: $i > $o] :
      ( ( X6 @ ( esk2_1 @ X6 ) )
      | ( ~ $true
        & $true )
      | ( X6 @ e )
      | ~ ( epred1_1 @ X6 ) ),
    inference(split_conjunct,[status(thm)],[c_0_8]) ).

thf(c_0_15,plain,
    ! [X6: $i > $o] :
      ( ( X6 @ e )
      | ~ ( X6 @ ( s @ ( esk2_1 @ X6 ) ) )
      | ~ ( epred1_1 @ X6 ) ),
    inference(cn,[status(thm)],[inference(cn,[status(thm)],[c_0_10])]) ).

thf(c_0_16,plain,
    ! [X6: $i > $o,X1: $i] :
      ( ( X6 @ ( s @ X1 ) )
      | ~ ( epred1_1 @ X6 )
      | ~ ( X6 @ X1 ) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(cn,[status(thm)],[c_0_11])]),c_0_12]) ).

thf(c_0_17,plain,
    ! [X22: $i,X23: $i,X24: $i > $o] :
      ( ( ~ ( epred2_0 @ X22 @ X23 )
        | ~ ( epred1_1 @ X24 )
        | ( X24 @ ( f @ X22 @ X23 ) ) )
      & ( ( epred1_1 @ ( epred3_2 @ X22 @ X23 ) )
        | ( epred2_0 @ X22 @ X23 ) )
      & ( ~ ( epred3_2 @ X22 @ X23 @ ( f @ X22 @ X23 ) )
        | ( epred2_0 @ X22 @ X23 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])])]) ).

thf(c_0_18,plain,
    ! [X6: $i > $o] :
      ( ( X6 @ ( esk2_1 @ X6 ) )
      | ( X6 @ e )
      | ~ ( epred1_1 @ X6 ) ),
    inference(cn,[status(thm)],[inference(cn,[status(thm)],[c_0_14])]) ).

thf(c_0_19,plain,
    ! [X6: $i > $o] :
      ( ( X6 @ e )
      | ~ ( X6 @ ( esk2_1 @ X6 ) )
      | ~ ( epred1_1 @ X6 ) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16]) ).

thf(c_0_20,plain,
    ! [X18: $i,X19: $i] :
      ( ( f @ ( s @ X18 ) @ ( s @ X19 ) )
      = ( f @ X18 @ ( f @ ( s @ X18 ) @ X19 ) ) ),
    inference(variable_rename,[status(thm)],[a3]) ).

thf(c_0_21,plain,
    ! [X16: $i] :
      ( ( f @ X16 @ e )
      = ( s @ e ) ),
    inference(variable_rename,[status(thm)],[a1]) ).

thf(c_0_22,plain,
    ! [X1: $i,X2: $i] :
      ( ( epred1_1 @ ( epred3_2 @ X1 @ X2 ) )
      | ( epred2_0 @ X1 @ X2 ) ),
    inference(split_conjunct,[status(thm)],[c_0_17]) ).

thf(c_0_23,plain,
    ! [X6: $i > $o] :
      ( ( X6 @ e )
      | ~ ( epred1_1 @ X6 ) ),
    inference(csr,[status(thm)],[c_0_18,c_0_19]) ).

thf(c_0_24,plain,
    ! [X1: $i,X2: $i,X6: $i > $o] :
      ( ( X6 @ ( f @ X1 @ X2 ) )
      | ~ ( epred2_0 @ X1 @ X2 )
      | ~ ( epred1_1 @ X6 ) ),
    inference(split_conjunct,[status(thm)],[c_0_17]) ).

thf(c_0_25,plain,
    ! [X1: $i,X2: $i] :
      ( ( f @ ( s @ X1 ) @ ( s @ X2 ) )
      = ( f @ X1 @ ( f @ ( s @ X1 ) @ X2 ) ) ),
    inference(split_conjunct,[status(thm)],[c_0_20]) ).

thf(c_0_26,plain,
    ! [X1: $i,X2: $i] :
      ( ( epred2_0 @ X1 @ X2 )
      | ~ ( epred3_2 @ X1 @ X2 @ ( f @ X1 @ X2 ) ) ),
    inference(split_conjunct,[status(thm)],[c_0_17]) ).

thf(c_0_27,plain,
    ! [X1: $i] :
      ( ( f @ X1 @ e )
      = ( s @ e ) ),
    inference(split_conjunct,[status(thm)],[c_0_21]) ).

thf(c_0_28,plain,
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( epred3_2 @ X1 @ X2 @ ( s @ X3 ) )
      | ( epred2_0 @ X1 @ X2 )
      | ~ ( epred3_2 @ X1 @ X2 @ X3 ) ),
    inference(spm,[status(thm)],[c_0_16,c_0_22]) ).

thf(c_0_29,plain,
    ! [X1: $i,X2: $i] :
      ( ( epred3_2 @ X1 @ X2 @ e )
      | ( epred2_0 @ X1 @ X2 ) ),
    inference(spm,[status(thm)],[c_0_23,c_0_22]) ).

thf(c_0_30,plain,
    ! [X17: $i] :
      ( ( f @ e @ ( s @ X17 ) )
      = ( s @ ( s @ ( f @ e @ X17 ) ) ) ),
    inference(variable_rename,[status(thm)],[a2]) ).

thf(c_0_31,plain,
    ! [X1: $i,X2: $i,X6: $i > $o] :
      ( ( X6 @ ( f @ ( s @ X1 ) @ ( s @ X2 ) ) )
      | ~ ( epred2_0 @ X1 @ ( f @ ( s @ X1 ) @ X2 ) )
      | ~ ( epred1_1 @ X6 ) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25]) ).

thf(c_0_32,plain,
    ! [X1: $i] :
      ( ( epred2_0 @ X1 @ e )
      | ~ ( epred3_2 @ X1 @ e @ ( s @ e ) ) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27]) ).

thf(c_0_33,plain,
    ! [X1: $i,X2: $i] :
      ( ( epred3_2 @ X1 @ X2 @ ( s @ e ) )
      | ( epred2_0 @ X1 @ X2 ) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29]) ).

thf(c_0_34,negated_conjecture,
    ~ ( d @ ( f @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) ) ),
    inference(fof_simplification,[status(thm)],[inference(assume_negation,[status(cth)],[conj_0])]) ).

thf(c_0_35,plain,
    ! [X1: $i] :
      ( ( f @ e @ ( s @ X1 ) )
      = ( s @ ( s @ ( f @ e @ X1 ) ) ) ),
    inference(split_conjunct,[status(thm)],[c_0_30]) ).

thf(c_0_36,plain,
    ! [X6: $i > $o] :
      ( ( epred1_1 @ X6 )
      | ~ ( X6 @ e )
      | ~ ( X6 @ ( s @ ( esk3_1 @ X6 ) ) )
      | ~ ( $true
          & $true ) ),
    inference(split_conjunct,[status(thm)],[c_0_8]) ).

thf(c_0_37,plain,
    ! [X20: $i] :
      ( ~ ( d @ X20 )
      | ( d @ ( s @ X20 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[a5])]) ).

thf(c_0_38,plain,
    ! [X1: $i,X2: $i,X6: $i > $o] :
      ( ( X6 @ ( f @ ( s @ X1 ) @ ( s @ X2 ) ) )
      | ~ ( epred2_0 @ ( s @ X1 ) @ X2 )
      | ~ ( epred1_1 @ ( epred2_0 @ X1 ) )
      | ~ ( epred1_1 @ X6 ) ),
    inference(spm,[status(thm)],[c_0_31,c_0_24]) ).

thf(c_0_39,plain,
    ! [X1: $i] :
      ( ( f @ ( s @ X1 ) @ ( s @ e ) )
      = ( f @ X1 @ ( s @ e ) ) ),
    inference(spm,[status(thm)],[c_0_25,c_0_27]) ).

thf(c_0_40,plain,
    ! [X1: $i] : ( epred2_0 @ X1 @ e ),
    inference(spm,[status(thm)],[c_0_32,c_0_33]) ).

thf(c_0_41,negated_conjecture,
    ~ ( d @ ( f @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) ) ),
    inference(split_conjunct,[status(thm)],[c_0_34]) ).

thf(c_0_42,plain,
    ( ( s @ ( s @ ( s @ e ) ) )
    = ( f @ e @ ( s @ e ) ) ),
    inference(spm,[status(thm)],[c_0_35,c_0_27]) ).

thf(c_0_43,plain,
    ! [X6: $i > $o] :
      ( ( X6 @ ( esk3_1 @ X6 ) )
      | ( epred1_1 @ X6 )
      | ~ ( X6 @ e )
      | ~ ( $true
          & $true ) ),
    inference(split_conjunct,[status(thm)],[c_0_8]) ).

thf(c_0_44,plain,
    ! [X6: $i > $o] :
      ( ( epred1_1 @ X6 )
      | ~ ( X6 @ ( s @ ( esk3_1 @ X6 ) ) )
      | ~ ( X6 @ e ) ),
    inference(cn,[status(thm)],[inference(cn,[status(thm)],[c_0_36])]) ).

thf(c_0_45,plain,
    ! [X1: $i] :
      ( ( d @ ( s @ X1 ) )
      | ~ ( d @ X1 ) ),
    inference(split_conjunct,[status(thm)],[c_0_37]) ).

thf(c_0_46,plain,
    d @ e,
    inference(split_conjunct,[status(thm)],[a4]) ).

thf(c_0_47,plain,
    ! [X1: $i,X6: $i > $o] :
      ( ( X6 @ ( f @ X1 @ ( s @ e ) ) )
      | ~ ( epred1_1 @ ( epred2_0 @ X1 ) )
      | ~ ( epred1_1 @ X6 ) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40])]) ).

thf(c_0_48,negated_conjecture,
    ( ~ ( epred2_0 @ ( s @ ( f @ e @ ( s @ e ) ) ) @ ( s @ ( f @ e @ ( s @ e ) ) ) )
    | ~ ( epred1_1 @ d ) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_24]),c_0_42]),c_0_42]) ).

thf(c_0_49,plain,
    ! [X6: $i > $o] :
      ( ( X6 @ ( esk3_1 @ X6 ) )
      | ( epred1_1 @ X6 )
      | ~ ( X6 @ e ) ),
    inference(cn,[status(thm)],[inference(cn,[status(thm)],[c_0_43])]) ).

thf(c_0_50,plain,
    ( ( epred1_1 @ d )
    | ~ ( d @ ( esk3_1 @ d ) ) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46])]) ).

thf(c_0_51,plain,
    ! [X1: $i,X6: $i > $o] :
      ( ( X6 @ ( f @ X1 @ ( s @ e ) ) )
      | ~ ( epred1_1 @ ( epred2_0 @ ( s @ X1 ) ) )
      | ~ ( epred1_1 @ X6 ) ),
    inference(spm,[status(thm)],[c_0_47,c_0_39]) ).

thf(c_0_52,negated_conjecture,
    ( ~ ( epred2_0 @ ( s @ ( f @ e @ ( s @ e ) ) ) @ ( f @ e @ ( s @ e ) ) )
    | ~ ( epred1_1 @ ( epred2_0 @ ( s @ ( f @ e @ ( s @ e ) ) ) ) )
    | ~ ( epred1_1 @ d ) ),
    inference(spm,[status(thm)],[c_0_48,c_0_16]) ).

thf(c_0_53,plain,
    epred1_1 @ d,
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_46]),c_0_50]) ).

thf(c_0_54,plain,
    ! [X1: $i,X2: $i] :
      ( ( epred2_0 @ X1 @ ( f @ ( s @ X1 ) @ X2 ) )
      | ~ ( epred3_2 @ X1 @ ( f @ ( s @ X1 ) @ X2 ) @ ( f @ ( s @ X1 ) @ ( s @ X2 ) ) ) ),
    inference(spm,[status(thm)],[c_0_26,c_0_25]) ).

thf(c_0_55,plain,
    ! [X1: $i,X6: $i > $o] :
      ( ( X6 @ ( f @ X1 @ ( s @ e ) ) )
      | ~ ( epred1_1 @ ( epred2_0 @ ( s @ ( s @ X1 ) ) ) )
      | ~ ( epred1_1 @ X6 ) ),
    inference(spm,[status(thm)],[c_0_51,c_0_39]) ).

thf(c_0_56,negated_conjecture,
    ( ~ ( epred2_0 @ ( s @ ( f @ e @ ( s @ e ) ) ) @ ( f @ e @ ( s @ e ) ) )
    | ~ ( epred1_1 @ ( epred2_0 @ ( s @ ( f @ e @ ( s @ e ) ) ) ) ) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_53])]) ).

thf(c_0_57,plain,
    ! [X1: $i,X6: $i > $o] :
      ( ( X6 @ ( f @ X1 @ ( s @ e ) ) )
      | ~ ( epred2_0 @ ( s @ X1 ) @ ( s @ e ) )
      | ~ ( epred1_1 @ X6 ) ),
    inference(spm,[status(thm)],[c_0_24,c_0_39]) ).

thf(c_0_58,plain,
    ! [X1: $i] :
      ( ( epred2_0 @ X1 @ ( s @ e ) )
      | ~ ( epred1_1 @ ( epred2_0 @ ( s @ ( s @ ( s @ X1 ) ) ) ) ) ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_27]),c_0_27]),c_0_22]) ).

thf(c_0_59,negated_conjecture,
    ( ~ ( epred1_1 @ ( epred2_0 @ ( s @ ( f @ e @ ( s @ e ) ) ) ) )
    | ~ ( epred2_0 @ ( s @ e ) @ ( s @ e ) ) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57]) ).

thf(c_0_60,plain,
    ! [X2: $i,X1: $i] :
      ( ( epred2_0 @ ( s @ X1 ) @ ( s @ X2 ) )
      | ~ ( epred2_0 @ ( s @ X1 ) @ X2 )
      | ~ ( epred1_1 @ ( epred2_0 @ X1 ) ) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_38]),c_0_22]) ).

thf(c_0_61,plain,
    ! [X1: $i] :
      ( ( epred2_0 @ X1 @ ( esk3_1 @ ( epred2_0 @ X1 ) ) )
      | ( epred1_1 @ ( epred2_0 @ X1 ) ) ),
    inference(spm,[status(thm)],[c_0_49,c_0_40]) ).

thf(c_0_62,plain,
    ~ ( epred1_1 @ ( epred2_0 @ ( s @ ( f @ e @ ( s @ e ) ) ) ) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_42]),c_0_59]) ).

thf(c_0_63,plain,
    ! [X1: $i] :
      ( ( epred1_1 @ ( epred2_0 @ ( s @ X1 ) ) )
      | ~ ( epred1_1 @ ( epred2_0 @ X1 ) ) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_60]),c_0_40])]),c_0_61]) ).

thf(c_0_64,plain,
    ~ ( epred1_1 @ ( epred2_0 @ ( f @ e @ ( s @ e ) ) ) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63]) ).

thf(c_0_65,plain,
    ! [X1: $i,X6: $i > $o] :
      ( ( X6 @ ( f @ e @ ( s @ X1 ) ) )
      | ~ ( X6 @ ( s @ ( f @ e @ X1 ) ) )
      | ~ ( epred1_1 @ X6 ) ),
    inference(spm,[status(thm)],[c_0_16,c_0_35]) ).

thf(c_0_66,plain,
    ~ ( epred1_1 @ ( epred2_0 @ ( s @ ( s @ e ) ) ) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_42]),c_0_64]) ).

thf(c_0_67,plain,
    ! [X1: $i] :
      ( ( epred2_0 @ e @ ( s @ X1 ) )
      | ~ ( epred3_2 @ e @ ( s @ X1 ) @ ( s @ ( f @ e @ X1 ) ) ) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_65]),c_0_22]) ).

thf(c_0_68,plain,
    ~ ( epred1_1 @ ( epred2_0 @ ( s @ e ) ) ),
    inference(spm,[status(thm)],[c_0_66,c_0_63]) ).

thf(c_0_69,plain,
    ! [X1: $i] :
      ( ( epred2_0 @ e @ ( s @ X1 ) )
      | ~ ( epred3_2 @ e @ ( s @ X1 ) @ ( f @ e @ X1 ) ) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_16]),c_0_22]) ).

thf(c_0_70,plain,
    ~ ( epred1_1 @ ( epred2_0 @ e ) ),
    inference(spm,[status(thm)],[c_0_68,c_0_63]) ).

thf(c_0_71,plain,
    ! [X1: $i] :
      ( ( epred2_0 @ e @ ( s @ X1 ) )
      | ~ ( epred2_0 @ e @ X1 ) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_24]),c_0_22]) ).

thf(c_0_72,plain,
    epred2_0 @ e @ ( esk3_1 @ ( epred2_0 @ e ) ),
    inference(spm,[status(thm)],[c_0_70,c_0_61]) ).

thf(c_0_73,plain,
    $false,
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_71]),c_0_40]),c_0_72])]),c_0_70]),
    [proof] ).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.30  % Problem    : theBenchmark.p : TPTP v0.0.0. Released v0.0.0.
% 0.11/0.32  % Command    : run_E %s %d THM
% 0.13/0.54  % Computer : n012.cluster.edu
% 0.13/0.54  % Model    : x86_64 x86_64
% 0.13/0.54  % CPU      : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.54  % Memory   : 8042.1875MB
% 0.13/0.54  % OS       : Linux 3.10.0-693.el7.x86_64
% 0.13/0.54  % CPULimit   : 300
% 0.13/0.54  % WCLimit    : 300
% 0.13/0.54  % DateTime   : Mon Aug  1 10:26:18 EDT 2022
% 0.13/0.54  % CPUTime    : 
% 0.19/0.68  Running higher-order on 8 cores theorem proving
% 0.19/0.68  Running: /export/starexec/sandbox/solver/bin/eprover-ho --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule=8 --cpu-limit=300 /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.19/0.69  # Version: 3.0pre003-ho
% 0.19/0.74  # partial match(1): HSMSSMSSSSSNFFN
% 0.19/0.74  # Preprocessing class: HSMSSMSSSSSNHFN.
% 0.19/0.74  # Scheduled 4 strats onto 8 cores with 300 seconds (2400 total)
% 0.19/0.74  # Starting new_ho_10 with 1500s (5) cores
% 0.19/0.74  # Starting new_bool_1 with 300s (1) cores
% 0.19/0.74  # Starting full_lambda_5 with 300s (1) cores
% 0.19/0.74  # Starting new_ho_10_unif with 300s (1) cores
% 0.19/0.74  # new_ho_10 with pid 22246 completed with status 0
% 0.19/0.74  # Result found by new_ho_10
% 0.19/0.74  # partial match(1): HSMSSMSSSSSNFFN
% 0.19/0.74  # Preprocessing class: HSMSSMSSSSSNHFN.
% 0.19/0.74  # Scheduled 4 strats onto 8 cores with 300 seconds (2400 total)
% 0.19/0.74  # Starting new_ho_10 with 1500s (5) cores
% 0.19/0.74  # No SInE strategy applied
% 0.19/0.74  # Search class: HGUSS-FFMF21-MHFFFMBN
% 0.19/0.74  # partial match(3): HGUSS-FFMF31-MHFMMMBN
% 0.19/0.74  # Scheduled 6 strats onto 5 cores with 1500 seconds (1500 total)
% 0.19/0.74  # Starting new_ho_10_cnf2 with 811s (1) cores
% 0.19/0.74  # Starting new_ho_10 with 151s (1) cores
% 0.19/0.74  # Starting post_as_ho1 with 136s (1) cores
% 0.19/0.74  # Starting new_ho_9 with 136s (1) cores
% 0.19/0.74  # Starting sh5l with 136s (1) cores
% 0.19/0.74  # new_ho_9 with pid 22256 completed with status 0
% 0.19/0.74  # Result found by new_ho_9
% 0.19/0.74  # partial match(1): HSMSSMSSSSSNFFN
% 0.19/0.74  # Preprocessing class: HSMSSMSSSSSNHFN.
% 0.19/0.74  # Scheduled 4 strats onto 8 cores with 300 seconds (2400 total)
% 0.19/0.74  # Starting new_ho_10 with 1500s (5) cores
% 0.19/0.74  # No SInE strategy applied
% 0.19/0.74  # Search class: HGUSS-FFMF21-MHFFFMBN
% 0.19/0.74  # partial match(3): HGUSS-FFMF31-MHFMMMBN
% 0.19/0.74  # Scheduled 6 strats onto 5 cores with 1500 seconds (1500 total)
% 0.19/0.74  # Starting new_ho_10_cnf2 with 811s (1) cores
% 0.19/0.74  # Starting new_ho_10 with 151s (1) cores
% 0.19/0.74  # Starting post_as_ho1 with 136s (1) cores
% 0.19/0.74  # Starting new_ho_9 with 136s (1) cores
% 0.19/0.74  # Preprocessing time       : 0.002 s
% 0.19/0.74  # Presaturation interreduction done
% 0.19/0.74  
% 0.19/0.74  # Proof found!
% 0.19/0.74  # SZS status Theorem
% 0.19/0.74  # SZS output start CNFRefutation
% See solution above
% 0.19/0.74  # Parsed axioms                        : 11
% 0.19/0.74  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.74  # Initial clauses                      : 68
% 0.19/0.74  # Removed in clause preprocessing      : 5
% 0.19/0.74  # Initial clauses in saturation        : 63
% 0.19/0.74  # Processed clauses                    : 363
% 0.19/0.74  # ...of these trivial                  : 38
% 0.19/0.74  # ...subsumed                          : 128
% 0.19/0.74  # ...remaining for further processing  : 197
% 0.19/0.74  # Other redundant clauses eliminated   : 0
% 0.19/0.74  # Clauses deleted for lack of memory   : 0
% 0.19/0.74  # Backward-subsumed                    : 16
% 0.19/0.74  # Backward-rewritten                   : 11
% 0.19/0.74  # Generated clauses                    : 970
% 0.19/0.74  # ...of the previous two non-redundant : 895
% 0.19/0.74  # ...aggressively subsumed             : 0
% 0.19/0.74  # Contextual simplify-reflections      : 26
% 0.19/0.74  # Paramodulations                      : 966
% 0.19/0.74  # Factorizations                       : 0
% 0.19/0.74  # NegExts                              : 0
% 0.19/0.74  # Equation resolutions                 : 0
% 0.19/0.74  # Propositional unsat checks           : 0
% 0.19/0.74  #    Propositional check models        : 0
% 0.19/0.74  #    Propositional check unsatisfiable : 0
% 0.19/0.74  #    Propositional clauses             : 0
% 0.19/0.74  #    Propositional clauses after purity: 0
% 0.19/0.74  #    Propositional unsat core size     : 0
% 0.19/0.74  #    Propositional preprocessing time  : 0.000
% 0.19/0.74  #    Propositional encoding time       : 0.000
% 0.19/0.74  #    Propositional solver time         : 0.000
% 0.19/0.74  #    Success case prop preproc time    : 0.000
% 0.19/0.74  #    Success case prop encoding time   : 0.000
% 0.19/0.74  #    Success case prop solver time     : 0.000
% 0.19/0.74  # Current number of processed clauses  : 148
% 0.19/0.74  #    Positive orientable unit clauses  : 27
% 0.19/0.74  #    Positive unorientable unit clauses: 1
% 0.19/0.74  #    Negative unit clauses             : 9
% 0.19/0.74  #    Non-unit-clauses                  : 111
% 0.19/0.74  # Current number of unprocessed clauses: 609
% 0.19/0.74  # ...number of literals in the above   : 1883
% 0.19/0.74  # Current number of archived formulas  : 0
% 0.19/0.74  # Current number of archived clauses   : 48
% 0.19/0.74  # Clause-clause subsumption calls (NU) : 4643
% 0.19/0.74  # Rec. Clause-clause subsumption calls : 4080
% 0.19/0.74  # Non-unit clause-clause subsumptions  : 152
% 0.19/0.74  # Unit Clause-clause subsumption calls : 376
% 0.19/0.74  # Rewrite failures with RHS unbound    : 0
% 0.19/0.74  # BW rewrite match attempts            : 24
% 0.19/0.74  # BW rewrite match successes           : 7
% 0.19/0.74  # Condensation attempts                : 363
% 0.19/0.74  # Condensation successes               : 0
% 0.19/0.74  # Termbank termtop insertions          : 26903
% 0.19/0.74  
% 0.19/0.74  # -------------------------------------------------
% 0.19/0.74  # User time                : 0.047 s
% 0.19/0.74  # System time              : 0.004 s
% 0.19/0.74  # Total time               : 0.051 s
% 0.19/0.74  # Maximum resident set size: 1992 pages
% 0.19/0.74  
% 0.19/0.74  # -------------------------------------------------
% 0.19/0.74  # User time                : 0.221 s
% 0.19/0.74  # System time              : 0.020 s
% 0.19/0.74  # Total time               : 0.241 s
% 0.19/0.74  # Maximum resident set size: 1732 pages
%------------------------------------------------------------------------------
