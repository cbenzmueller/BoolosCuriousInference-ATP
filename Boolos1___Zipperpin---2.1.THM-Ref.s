%------------------------------------------------------------------------------
% File     : Zipperpin---2.1
% Problem  : theBenchmark.p : TPTP v0.0.0. Released v0.0.0.
% Transfm  : none
% Format   : tptp:raw
% Command  : python3 /export/starexec/sandbox2/solver/bin/portfolio.lams.parallel.py %s %d /export/starexec/sandbox2/tmp/tmp.cqfSlcyd5i true

% Computer : n018.cluster.edu
% Model    : x86_64 x86_64
% CPU      : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory   : 8042.1875MB
% OS       : Linux 3.10.0-693.el7.x86_64
% CPULimit : 300s
% WCLimit  : 300s
% DateTime : Mon Aug  1 10:14:15 EDT 2022

% Result   : Theorem 85.70s 11.54s
% Output   : Refutation 85.70s
% Verified : 
% SZS Type : Refutation
%            Derivation depth      :    6
%            Number of leaves      :   17
% Syntax   : Number of formulae    :   54 (  26 unt;   8 typ;   0 def)
%            Number of atoms       :   84 (  10 equ;   0 cnn)
%            Maximal formula atoms :    5 (   1 avg)
%            Number of connectives :  329 (  33   ~;  38   |;   1   &; 251   @)
%                                         (   2 <=>;   4  =>;   0  <=;   0 <~>)
%            Maximal formula depth :   11 (   6 avg)
%            Number of types       :    2 (   0 usr)
%            Number of type conns  :   28 (  28   >;   0   *;   0   +;   0  <<)
%            Number of symbols     :   10 (   8 usr;   2 con; 0-3 aty)
%            Number of variables   :   65 (   9   ^  56   !;   0   ?;  65   :)

% Comments : 
%------------------------------------------------------------------------------
thf(f_type,type,
    f: $i > $i > $i ).

thf(sk__type,type,
    sk_: ( $i > $o ) > $i ).

thf(s_type,type,
    s: $i > $i ).

thf(p_type,type,
    p: $i > $i > $o ).

thf(isIndSet_type,type,
    isIndSet: ( $i > $o ) > $o ).

thf(d_type,type,
    d: $i > $o ).

thf(e_type,type,
    e: $i ).

thf(sk__1_type,type,
    sk__1: $i > $i > $i > $o ).

thf(p_def,axiom,
    ( p
    = ( ^ [X: $i,Y: $i] :
          ( ^ [X2: $i] :
            ! [X3: $i > $o] :
              ( ( isIndSet @ X3 )
             => ( X3 @ X2 ) )
          @ ( f @ X @ Y ) ) ) ) ).

thf(zf_stmt_0,axiom,
    ! [V_1: $i,V_2: $i] :
      ( ( p @ V_1 @ V_2 )
    <=> ! [X4: $i > $o] :
          ( ( isIndSet @ X4 )
         => ( X4 @ ( f @ V_1 @ V_2 ) ) ) ) ).

thf(zip_derived_cl9,plain,
    ! [X0: $i > $o,X1: $i,X2: $i] :
      ( ~ ( isIndSet @ X0 )
      | ( X0 @ ( f @ X1 @ X2 ) )
      | ~ ( p @ X1 @ X2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0]) ).

thf(conj_0,conjecture,
    d @ ( f @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) ) ).

thf(zf_stmt_1,negated_conjecture,
    ~ ( d @ ( f @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[conj_0]) ).

thf(zip_derived_cl12,plain,
    ~ ( d @ ( f @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1]) ).

thf(zip_derived_cl363,plain,
    ( ~ ( p @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) )
    | ~ ( isIndSet @ d ) ),
    inference('sup-',[status(thm)],[zip_derived_cl9,zip_derived_cl12]) ).

thf(a4,axiom,
    d @ e ).

thf(zip_derived_cl3,plain,
    d @ e,
    inference(cnf,[status(esa)],[a4]) ).

thf(isIndSet_def,axiom,
    ! [Q: $i > $o] :
      ( ( isIndSet @ Q )
    <=> ( ( Q @ e )
        & ! [X: $i] :
            ( ( Q @ X )
           => ( Q @ ( s @ X ) ) ) ) ) ).

thf(zip_derived_cl7,plain,
    ! [X0: $i > $o] :
      ( ( isIndSet @ X0 )
      | ( X0 @ ( sk_ @ X0 ) )
      | ~ ( X0 @ e ) ),
    inference(cnf,[status(esa)],[isIndSet_def]) ).

thf(zip_derived_cl157,plain,
    ( ( ^ [Y0: $i] :
          ( d
          @ ( ^ [Y1: $i] : Y1
            @ Y0 ) )
      @ ( sk_
        @ ^ [Y0: $i] :
            ( d
            @ ( ^ [Y1: $i] : Y1
              @ Y0 ) ) ) )
    | ( isIndSet
      @ ^ [Y0: $i] :
          ( d
          @ ( ^ [Y1: $i] : Y1
            @ Y0 ) ) ) ),
    inference('sup-',[status(thm)],[zip_derived_cl3,zip_derived_cl7]) ).

thf(zip_derived_cl177,plain,
    ( ( d @ ( sk_ @ d ) )
    | ( isIndSet @ d ) ),
    inference(ho_norm,[status(thm)],[zip_derived_cl157]) ).

thf(a5,axiom,
    ! [X: $i] :
      ( ( d @ X )
     => ( d @ ( s @ X ) ) ) ).

thf(zip_derived_cl4,plain,
    ! [X0: $i] :
      ( ( d @ ( s @ X0 ) )
      | ~ ( d @ X0 ) ),
    inference(cnf,[status(esa)],[a5]) ).

thf(zip_derived_cl8,plain,
    ! [X0: $i > $o] :
      ( ( isIndSet @ X0 )
      | ~ ( X0 @ ( s @ ( sk_ @ X0 ) ) )
      | ~ ( X0 @ e ) ),
    inference(cnf,[status(esa)],[isIndSet_def]) ).

thf(zip_derived_cl282,plain,
    ( ~ ( d @ ( sk_ @ d ) )
    | ~ ( d @ e )
    | ( isIndSet @ d ) ),
    inference('sup-',[status(thm)],[zip_derived_cl4,zip_derived_cl8]) ).

thf(zip_derived_cl3_001,plain,
    d @ e,
    inference(cnf,[status(esa)],[a4]) ).

thf(zip_derived_cl320,plain,
    ( ~ ( d @ ( sk_ @ d ) )
    | ( isIndSet @ d ) ),
    inference(demod,[status(thm)],[zip_derived_cl282,zip_derived_cl3]) ).

thf(zip_derived_cl475,plain,
    isIndSet @ d,
    inference(clc,[status(thm)],[zip_derived_cl177,zip_derived_cl320]) ).

thf(zip_derived_cl476,plain,
    ~ ( p @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) ),
    inference(demod,[status(thm)],[zip_derived_cl363,zip_derived_cl475]) ).

thf(a2,axiom,
    ! [Y: $i] :
      ( ( f @ e @ ( s @ Y ) )
      = ( s @ ( s @ ( f @ e @ Y ) ) ) ) ).

thf(zip_derived_cl1,plain,
    ! [X0: $i] :
      ( ( f @ e @ ( s @ X0 ) )
      = ( s @ ( s @ ( f @ e @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[a2]) ).

thf(zip_derived_cl9_002,plain,
    ! [X0: $i > $o,X1: $i,X2: $i] :
      ( ~ ( isIndSet @ X0 )
      | ( X0 @ ( f @ X1 @ X2 ) )
      | ~ ( p @ X1 @ X2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0]) ).

thf(zip_derived_cl6,plain,
    ! [X0: $i > $o,X1: $i] :
      ( ~ ( X0 @ X1 )
      | ( X0 @ ( s @ X1 ) )
      | ~ ( isIndSet @ X0 ) ),
    inference(cnf,[status(esa)],[isIndSet_def]) ).

thf(a1,axiom,
    ! [N: $i] :
      ( ( f @ N @ e )
      = ( s @ e ) ) ).

thf(zip_derived_cl0,plain,
    ! [X0: $i] :
      ( ( f @ X0 @ e )
      = ( s @ e ) ),
    inference(cnf,[status(esa)],[a1]) ).

thf(zip_derived_cl1_003,plain,
    ! [X0: $i] :
      ( ( f @ e @ ( s @ X0 ) )
      = ( s @ ( s @ ( f @ e @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[a2]) ).

thf(zip_derived_cl14,plain,
    ( ( f @ e @ ( s @ e ) )
    = ( s @ ( s @ ( s @ e ) ) ) ),
    inference('sup+',[status(thm)],[zip_derived_cl0,zip_derived_cl1]) ).

thf(zip_derived_cl11,plain,
    ! [X0: $i,X1: $i] :
      ( ( p @ X0 @ X1 )
      | ( isIndSet @ ( sk__1 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0]) ).

thf(zip_derived_cl8_004,plain,
    ! [X0: $i > $o] :
      ( ( isIndSet @ X0 )
      | ~ ( X0 @ ( s @ ( sk_ @ X0 ) ) )
      | ~ ( X0 @ e ) ),
    inference(cnf,[status(esa)],[isIndSet_def]) ).

thf(zip_derived_cl5,plain,
    ! [X0: $i > $o] :
      ( ( X0 @ e )
      | ~ ( isIndSet @ X0 ) ),
    inference(cnf,[status(esa)],[isIndSet_def]) ).

thf(zip_derived_cl11_005,plain,
    ! [X0: $i,X1: $i] :
      ( ( p @ X0 @ X1 )
      | ( isIndSet @ ( sk__1 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0]) ).

thf(zip_derived_cl29,plain,
    ! [X0: $i,X1: $i] :
      ( ( sk__1 @ X1 @ X0 @ e )
      | ( p @ X0 @ X1 ) ),
    inference('sup+',[status(thm)],[zip_derived_cl5,zip_derived_cl11]) ).

thf(zip_derived_cl7_006,plain,
    ! [X0: $i > $o] :
      ( ( isIndSet @ X0 )
      | ( X0 @ ( sk_ @ X0 ) )
      | ~ ( X0 @ e ) ),
    inference(cnf,[status(esa)],[isIndSet_def]) ).

thf(a3,axiom,
    ! [X: $i,Y: $i] :
      ( ( f @ ( s @ X ) @ ( s @ Y ) )
      = ( f @ X @ ( f @ ( s @ X ) @ Y ) ) ) ).

thf(zip_derived_cl2,plain,
    ! [X0: $i,X1: $i] :
      ( ( f @ ( s @ X0 ) @ ( s @ X1 ) )
      = ( f @ X0 @ ( f @ ( s @ X0 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[a3]) ).

thf(zip_derived_cl6_007,plain,
    ! [X0: $i > $o,X1: $i] :
      ( ~ ( X0 @ X1 )
      | ( X0 @ ( s @ X1 ) )
      | ~ ( isIndSet @ X0 ) ),
    inference(cnf,[status(esa)],[isIndSet_def]) ).

thf(zip_derived_cl11_008,plain,
    ! [X0: $i,X1: $i] :
      ( ( p @ X0 @ X1 )
      | ( isIndSet @ ( sk__1 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0]) ).

thf(zip_derived_cl57,plain,
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( sk__1 @ X1 @ X0 @ ( s @ X2 ) )
      | ~ ( sk__1 @ X1 @ X0 @ X2 )
      | ( p @ X0 @ X1 ) ),
    inference('sup+',[status(thm)],[zip_derived_cl6,zip_derived_cl11]) ).

thf(zip_derived_cl0_009,plain,
    ! [X0: $i] :
      ( ( f @ X0 @ e )
      = ( s @ e ) ),
    inference(cnf,[status(esa)],[a1]) ).

thf(zip_derived_cl9_010,plain,
    ! [X0: $i > $o,X1: $i,X2: $i] :
      ( ~ ( isIndSet @ X0 )
      | ( X0 @ ( f @ X1 @ X2 ) )
      | ~ ( p @ X1 @ X2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0]) ).

thf(zip_derived_cl9_011,plain,
    ! [X0: $i > $o,X1: $i,X2: $i] :
      ( ~ ( isIndSet @ X0 )
      | ( X0 @ ( f @ X1 @ X2 ) )
      | ~ ( p @ X1 @ X2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0]) ).

thf(zip_derived_cl195,plain,
    ! [X0: $i,X1: $i,X2: $i,X3: $i > $o] :
      ( ( X3 @ ( f @ X0 @ ( f @ X2 @ X1 ) ) )
      | ~ ( isIndSet @ X3 )
      | ~ ( p @ X2 @ X1 )
      | ~ ( isIndSet @ ( p @ X0 ) ) ),
    inference('sup+',[status(thm)],[zip_derived_cl9,zip_derived_cl9]) ).

thf(zip_derived_cl10,plain,
    ! [X0: $i,X1: $i] :
      ( ( p @ X0 @ X1 )
      | ~ ( sk__1 @ X1 @ X0 @ ( f @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0]) ).

thf(zip_derived_cl8532,plain,
    $false,
    inference(eprover,[status(thm)],[zip_derived_cl476,zip_derived_cl1,zip_derived_cl9,zip_derived_cl6,zip_derived_cl14,zip_derived_cl11,zip_derived_cl8,zip_derived_cl29,zip_derived_cl7,zip_derived_cl2,zip_derived_cl57,zip_derived_cl0,zip_derived_cl195,zip_derived_cl10]) ).


%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.22  % Problem  : theBenchmark.p : TPTP v0.0.0. Released v0.0.0.
% 0.10/0.23  % Command  : python3 /export/starexec/sandbox2/solver/bin/portfolio.lams.parallel.py %s %d /export/starexec/sandbox2/tmp/tmp.cqfSlcyd5i true
% 0.13/0.46  % Computer : n018.cluster.edu
% 0.13/0.46  % Model    : x86_64 x86_64
% 0.13/0.46  % CPU      : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.46  % Memory   : 8042.1875MB
% 0.13/0.46  % OS       : Linux 3.10.0-693.el7.x86_64
% 0.13/0.46  % CPULimit : 300
% 0.13/0.46  % WCLimit  : 300
% 0.13/0.46  % DateTime : Mon Aug  1 10:30:22 EDT 2022
% 0.13/0.46  % CPUTime  : 
% 0.13/0.46  % Running portfolio for 300 s
% 0.13/0.46  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.46  % Number of cores: 8
% 0.13/0.46  % Python version: Python 3.6.8
% 0.13/0.46  % Running in HO mode
% 0.33/0.77  % Total configuration time : 828
% 0.33/0.77  % Estimated wc time : 1656
% 0.33/0.77  % Estimated cpu time (8 cpus) : 207.0
% 0.33/0.85  % /export/starexec/sandbox2/solver/bin/lams/40_c.s.sh running for 80s
% 0.33/0.85  % /export/starexec/sandbox2/solver/bin/lams/35_full_unif4.sh running for 80s
% 0.33/0.86  % /export/starexec/sandbox2/solver/bin/lams/40_c_ic.sh running for 80s
% 0.33/0.86  % /export/starexec/sandbox2/solver/bin/lams/15_e_short1.sh running for 30s
% 0.34/0.86  % /export/starexec/sandbox2/solver/bin/lams/20_acsne_simpl.sh running for 40s
% 0.34/0.86  % /export/starexec/sandbox2/solver/bin/lams/40_b.comb.sh running for 70s
% 0.34/0.86  % /export/starexec/sandbox2/solver/bin/lams/40_noforms.sh running for 90s
% 0.34/0.87  % /export/starexec/sandbox2/solver/bin/lams/30_sp5.sh running for 60s
% 85.70/11.54  % Solved by lams/40_c_ic.sh.
% 85.70/11.54  % running E: timeout 27 /export/starexec/sandbox2/solver/bin/lams/eprover-ho --pos-ext=all --neg-ext=all /export/starexec/sandbox2/tmp/tmp.cqfSlcyd5i/e_inputa57f79 --cpu-limit=25 --auto-schedule -s -p
% 85.70/11.54  % done 882 iterations in 10.644s
% 85.70/11.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 85.70/11.54  % SZS output start Refutation
% See solution above
% 85.70/11.54  
% 85.70/11.54  
% 85.70/11.54  % Terminating...
% 85.94/11.63  % Runner terminated.
% 85.94/11.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
