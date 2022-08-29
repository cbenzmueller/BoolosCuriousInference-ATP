%------------------------------------------------------------------------------
% File     : Leo-III---1.7.0
% Problem  : theBenchmark.p : TPTP v0.0.0. Released v0.0.0.
% Transfm  : none
% Format   : tptp:raw
% Command  : run_Leo-III %s %d

% Computer : n007.cluster.edu
% Model    : x86_64 x86_64
% CPU      : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory   : 8042.1875MB
% OS       : Linux 3.10.0-693.el7.x86_64
% CPULimit : 300s
% WCLimit  : 300s
% DateTime : Mon Aug  1 10:14:13 EDT 2022

% Result   : Theorem 230.96s 49.63s
% Output   : Refutation 231.48s
% Verified : 
% SZS Type : Refutation
%            Derivation depth      :   36
%            Number of leaves      :   29
% Syntax   : Number of formulae    :  495 ( 162 unt;  21 typ;   0 def)
%            Number of atoms       : 2189 ( 600 equ;   0 cnn)
%            Maximal formula atoms :    7 (   4 avg)
%            Number of connectives : 5725 ( 567   ~; 377   |;  43   &;4479   @)
%                                         (   0 <=>; 259  =>;   0  <=;   0 <~>)
%            Maximal formula depth :   16 (   4 avg)
%            Number of types       :    2 (   0 usr)
%            Number of type conns  :  174 ( 174   >;   0   *;   0   +;   0  <<)
%            Number of symbols     :   24 (  21 usr;  17 con; 0-2 aty)
%            Number of variables   : 1010 ( 540   ^ 470   !;   0   ?;1010   :)

% Comments : 
%------------------------------------------------------------------------------
thf(e_type,type,
    e: $i ).

thf(s_type,type,
    s: $i > $i ).

thf(d_type,type,
    d: $i > $o ).

thf(f_type,type,
    f: $i > $i > $i ).

thf(isIndSet_type,type,
    isIndSet: ( $i > $o ) > $o ).

thf(p_type,type,
    p: $i > $i > $o ).

thf(sk1_type,type,
    sk1: ( $i > $o ) > $i ).

thf(sk2_type,type,
    sk2: $i ).

thf(sk3_type,type,
    sk3: $i ).

thf(sk6_type,type,
    sk6: $i ).

thf(sk8_type,type,
    sk8: $i ).

thf(sk9_type,type,
    sk9: $i ).

thf(sk10_type,type,
    sk10: $i ).

thf(sk23_type,type,
    sk23: $i ).

thf(sk66_type,type,
    sk66: $i ).

thf(sk68_type,type,
    sk68: $i ).

thf(sk69_type,type,
    sk69: $i ).

thf(sk71_type,type,
    sk71: $i ).

thf(sk91_type,type,
    sk91: $i ).

thf(sk94_type,type,
    sk94: $i ).

thf(sk211_type,type,
    sk211: $i ).

thf(8,axiom,
    ( isIndSet
    = ( ^ [A: $i > $o] :
          ( ( A @ e )
          & ! [B: $i] :
              ( ( A @ B )
             => ( A @ ( s @ B ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',isIndSet_def) ).

thf(23,plain,
    ( isIndSet
    = ( ^ [A: $i > $o] :
          ( ( A @ e )
          & ! [B: $i] :
              ( ( A @ B )
             => ( A @ ( s @ B ) ) ) ) ) ),
    inference(defexp_and_simp_and_etaexpand,[status(thm)],[8]) ).

thf(24,plain,
    ( ( ^ [A: $i > $o] :
          ( ( A @ e )
          & ! [B: $i] :
              ( ( A @ B )
             => ( A @ ( s @ B ) ) ) ) )
    = isIndSet ),
    inference(lifteq,[status(thm)],[23]) ).

thf(27,plain,
    ! [A: $i > $o] :
      ( ( ( A @ e )
        & ! [B: $i] :
            ( ( A @ B )
           => ( A @ ( s @ B ) ) ) )
      = ( isIndSet @ A ) ),
    inference(func_ext,[status(esa)],[24]) ).

thf(59,plain,
    ! [B: $i > $o,A: $i > $o] :
      ( ( ( ( isIndSet @ A )
          & ! [C: $i] :
              ( ( B @ C )
             => ( B @ ( s @ C ) ) ) )
        = ( isIndSet @ B ) )
      | ( ( ( A @ e )
          & ! [C: $i] :
              ( ( A @ C )
             => ( A @ ( s @ C ) ) ) )
       != ( B @ e ) ) ),
    inference(paramod_ordered,[status(thm)],[27,27]) ).

thf(62,plain,
    ! [C: $i > $i > $o,B: $i > $i > $o,A: $i > $o] :
      ( ( ( ( isIndSet @ ( B @ e ) )
          & ! [D: $i] :
              ( ( ( A @ D )
                & ! [E: $i] :
                    ( ( B @ D @ E )
                   => ( C @ D @ E ) ) )
             => ( ( A @ ( s @ D ) )
                & ! [E: $i] :
                    ( ( B @ ( s @ D ) @ E )
                   => ( C @ ( s @ D ) @ E ) ) ) ) )
        = ( isIndSet
          @ ^ [D: $i] :
              ( ( A @ D )
              & ! [E: $i] :
                  ( ( B @ D @ E )
                 => ( C @ D @ E ) ) ) ) )
      | ( ( B @ e @ e )
       != ( A @ e ) )
      | ( ( ^ [D: $i] : ( B @ e @ ( s @ D ) ) )
       != ( C @ e ) ) ),
    inference(pre_uni,[status(thm)],[59:[bind(A,$thf( F @ e )),bind(B,$thf( ^ [F: $i] : ( ( C @ F ) & ! [G: $i] : ( ( F @ F @ G ) => ( G @ F @ G ) ) ) ))]]) ).

thf(63,plain,
    ! [C: $i > $i > $o,B: $i > $i > $o,A: $i > $o] :
      ( ( ( ( isIndSet @ ( B @ e ) )
          & ! [D: $i] :
              ( ( ( A @ D )
                & ! [E: $i] :
                    ( ( B @ D @ E )
                   => ( C @ D @ E ) ) )
             => ( ( A @ ( s @ D ) )
                & ! [E: $i] :
                    ( ( B @ ( s @ D ) @ E )
                   => ( C @ ( s @ D ) @ E ) ) ) ) )
        = ( isIndSet
          @ ^ [D: $i] :
              ( ( A @ D )
              & ! [E: $i] :
                  ( ( B @ D @ E )
                 => ( C @ D @ E ) ) ) ) )
      | ( ( B @ e @ e )
       != ( A @ e ) )
      | ( ( ^ [D: $i] : ( B @ e @ ( s @ D ) ) )
       != ( C @ e ) ) ),
    inference(pre_uni,[status(thm)],[62:[]]) ).

thf(69,plain,
    ! [C: $i > $i > $o,B: $i > $i > $o,A: $i > $o] :
      ( ( ( ( isIndSet @ ( B @ e ) )
          & ! [D: $i] :
              ( ( ( A @ D )
                & ! [E: $i] :
                    ( ( B @ D @ E )
                   => ( C @ D @ E ) ) )
             => ( ( A @ ( s @ D ) )
                & ! [E: $i] :
                    ( ( B @ ( s @ D ) @ E )
                   => ( C @ ( s @ D ) @ E ) ) ) ) )
        = ( isIndSet
          @ ^ [D: $i] :
              ( ( A @ D )
              & ! [E: $i] :
                  ( ( B @ D @ E )
                 => ( C @ D @ E ) ) ) ) )
      | ( ( B @ e @ e )
       != ( A @ e ) )
      | ( ( ^ [D: $i] : ( B @ e @ ( s @ D ) ) )
       != ( C @ e ) ) ),
    inference(simp,[status(thm)],[63]) ).

thf(6,axiom,
    d @ e,
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',a4) ).

thf(20,plain,
    d @ e,
    inference(defexp_and_simp_and_etaexpand,[status(thm)],[6]) ).

thf(58,plain,
    ! [A: $i > $o] :
      ( ( ( ! [B: $i] :
              ( ( A @ B )
             => ( A @ ( s @ B ) ) ) )
        = ( isIndSet @ A ) )
      | ( ( d @ e )
       != ( A @ e ) ) ),
    inference(paramod_ordered,[status(thm)],[20,27]) ).

thf(60,plain,
    ( ( ! [A: $i] :
          ( ( d @ e )
         => ( d @ e ) ) )
    = ( isIndSet
      @ ^ [A: $i] : ( d @ e ) ) ),
    inference(pre_uni,[status(thm)],[58:[bind(A,$thf( ^ [B: $i] : ( d @ e ) ))]]) ).

thf(68,plain,
    ( isIndSet
    @ ^ [A: $i] : ( d @ e ) ),
    inference(simp,[status(thm)],[60]) ).

thf(70,plain,
    ( isIndSet
    @ ^ [A: $i] : $true ),
    inference(rewrite,[status(thm)],[68,20]) ).

thf(57,plain,
    ! [A: $i > $o] :
      ( ( ( A @ e )
        & ! [B: $i] :
            ( ( A @ B )
           => ( A @ ( s @ B ) ) ) )
      | ~ ( isIndSet @ A ) ),
    inference(bool_ext,[status(thm)],[27]) ).

thf(67,plain,
    ! [A: $i > $o] :
      ( ~ ( isIndSet @ A )
      | ( A @ e ) ),
    inference(cnf,[status(esa)],[57]) ).

thf(7,axiom,
    ! [A: $i] :
      ( ( d @ A )
     => ( d @ ( s @ A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',a5) ).

thf(21,plain,
    ! [A: $i] :
      ( ( d @ A )
     => ( d @ ( s @ A ) ) ),
    inference(defexp_and_simp_and_etaexpand,[status(thm)],[7]) ).

thf(22,plain,
    ! [A: $i] :
      ( ~ ( d @ A )
      | ( d @ ( s @ A ) ) ),
    inference(cnf,[status(esa)],[21]) ).

thf(61,plain,
    ( ( ! [A: $i] :
          ( ( d @ A )
         => ( d @ ( s @ A ) ) ) )
    = ( isIndSet @ d ) ),
    inference(pre_uni,[status(thm)],[58:[bind(A,$thf( d ))]]) ).

thf(82,plain,
    ! [A: $i > $o] :
      ( ( ( ( isIndSet @ d )
          & ! [B: $i] :
              ( ( A @ B )
             => ( A @ ( s @ B ) ) ) )
        = ( isIndSet @ A ) )
      | ( ( ! [B: $i] :
              ( ( d @ B )
             => ( d @ ( s @ B ) ) ) )
       != ( A @ e ) ) ),
    inference(paramod_ordered,[status(thm)],[61,27]) ).

thf(89,plain,
    ( ( ( isIndSet @ d )
      & ! [A: $i] :
          ( ! [B: $i] :
              ( ( d @ B )
             => ( d @ ( s @ B ) ) )
         => ! [B: $i] :
              ( ( d @ B )
             => ( d @ ( s @ B ) ) ) ) )
    = ( isIndSet
      @ ^ [A: $i] :
        ! [B: $i] :
          ( ( d @ B )
         => ( d @ ( s @ B ) ) ) ) ),
    inference(pre_uni,[status(thm)],[82:[bind(A,$thf( ^ [B: $i] : ! [C: $i] : ( ( d @ C ) => ( d @ ( s @ C ) ) ) ))]]) ).

thf(94,plain,
    ( ( isIndSet @ d )
    = ( isIndSet
      @ ^ [A: $i] :
        ! [B: $i] :
          ( ( d @ B )
         => ( d @ ( s @ B ) ) ) ) ),
    inference(simp,[status(thm)],[89]) ).

thf(112,plain,
    ( ( isIndSet
      @ ^ [A: $i] :
        ! [B: $i] :
          ( ( d @ B )
         => ( d @ ( s @ B ) ) ) )
    = ( ! [A: $i] :
          ( ( d @ A )
         => ( d @ ( s @ A ) ) ) ) ),
    inference(rewrite,[status(thm)],[61,94]) ).

thf(1044,plain,
    ( ( isIndSet @ d )
    = ( ! [A: $i] :
          ( ( d @ A )
         => ( d @ ( s @ A ) ) ) ) ),
    inference(rewrite,[status(thm)],[94,112]) ).

thf(2325,plain,
    ( ~ ( isIndSet
        @ ^ [A: $i] : $false )
    | $false ),
    inference(prim_subst,[status(thm)],[67:[bind(A,$thf( ^ [B: $i] : $false ))]]) ).

thf(2403,plain,
    ~ ( isIndSet
      @ ^ [A: $i] : $false ),
    inference(simp,[status(thm)],[2325]) ).

thf(2447,plain,
    ( ~ ! [A: $i] :
          ( ( d @ A )
         => ( d @ ( s @ A ) ) )
    | ( ( isIndSet @ d )
     != ( isIndSet
        @ ^ [A: $i] : $false ) ) ),
    inference(paramod_ordered,[status(thm)],[1044,2403]) ).

thf(2471,plain,
    ( ~ ! [A: $i] :
          ( ( d @ A )
         => ( d @ ( s @ A ) ) )
    | ( d
     != ( ^ [A: $i] : $false ) ) ),
    inference(simp,[status(thm)],[2447]) ).

thf(2481,plain,
    ( ( d
     != ( ^ [A: $i] : $false ) )
    | ~ ( d @ ( s @ sk69 ) ) ),
    inference(cnf,[status(esa)],[2471]) ).

thf(2988,plain,
    ! [A: $i] :
      ( ~ ( d @ A )
      | ( d
       != ( ^ [B: $i] : $false ) )
      | ( ( d @ ( s @ A ) )
       != ( d @ ( s @ sk69 ) ) ) ),
    inference(paramod_ordered,[status(thm)],[22,2481]) ).

thf(2989,plain,
    ( ~ ( d @ sk69 )
    | ( d
     != ( ^ [A: $i] : $false ) ) ),
    inference(pattern_uni,[status(thm)],[2988:[bind(A,$thf( sk69 ))]]) ).

thf(3466,plain,
    ! [A: $i > $o] :
      ( ~ ( isIndSet @ A )
      | ( d
       != ( ^ [B: $i] : $false ) )
      | ( ( A @ e )
       != ( d @ sk69 ) ) ),
    inference(paramod_ordered,[status(thm)],[67,2989]) ).

thf(3471,plain,
    ( ~ ( isIndSet
        @ ^ [A: $i] : ( d @ sk69 ) )
    | ( d
     != ( ^ [A: $i] : $false ) ) ),
    inference(pre_uni,[status(thm)],[3466:[bind(A,$thf( ^ [B: $i] : ( d @ sk69 ) ))]]) ).

thf(3923,plain,
    ( ( d
     != ( ^ [A: $i] : $false ) )
    | ( ( isIndSet
        @ ^ [A: $i] : ( d @ sk69 ) )
     != ( isIndSet
        @ ^ [A: $i] : $true ) ) ),
    inference(paramod_ordered,[status(thm)],[70,3471]) ).

thf(3962,plain,
    ( ( d
     != ( ^ [A: $i] : $false ) )
    | ( ( ^ [A: $i] : ( d @ sk69 ) )
     != ( ^ [A: $i] : $true ) ) ),
    inference(simp,[status(thm)],[3923]) ).

thf(249,plain,
    ! [A: $i] :
      ( ( d @ ( s @ A ) )
      | ( ( d @ e )
       != ( d @ A ) ) ),
    inference(paramod_ordered,[status(thm)],[20,22]) ).

thf(250,plain,
    d @ ( s @ e ),
    inference(pattern_uni,[status(thm)],[249:[bind(A,$thf( e ))]]) ).

thf(265,plain,
    ! [A: $i > $o] :
      ( ( ( ! [B: $i] :
              ( ( A @ B )
             => ( A @ ( s @ B ) ) ) )
        = ( isIndSet @ A ) )
      | ( ( d @ ( s @ e ) )
       != ( A @ e ) ) ),
    inference(paramod_ordered,[status(thm)],[250,27]) ).

thf(268,plain,
    ( ( ! [A: $i] :
          ( ( d @ ( s @ A ) )
         => ( d @ ( s @ ( s @ A ) ) ) ) )
    = ( isIndSet
      @ ^ [A: $i] : ( d @ ( s @ A ) ) ) ),
    inference(pre_uni,[status(thm)],[265:[bind(A,$thf( ^ [B: $i] : ( d @ ( s @ B ) ) ))]]) ).

thf(779,plain,
    ! [A: $i > $o] :
      ( ( ( ! [B: $i] :
              ( ( d @ ( s @ B ) )
             => ( d @ ( s @ ( s @ B ) ) ) )
          & ! [B: $i] :
              ( ( A @ B )
             => ( A @ ( s @ B ) ) ) )
        = ( isIndSet @ A ) )
      | ( ( isIndSet
          @ ^ [B: $i] : ( d @ ( s @ B ) ) )
       != ( A @ e ) ) ),
    inference(paramod_ordered,[status(thm)],[268,27]) ).

thf(794,plain,
    ( ( ! [A: $i] :
          ( ( d @ ( s @ A ) )
         => ( d @ ( s @ ( s @ A ) ) ) )
      & ! [A: $i] :
          ( ( isIndSet
            @ ^ [B: $i] : ( d @ ( s @ B ) ) )
         => ( isIndSet
            @ ^ [B: $i] : ( d @ ( s @ B ) ) ) ) )
    = ( isIndSet
      @ ^ [A: $i] :
          ( isIndSet
          @ ^ [B: $i] : ( d @ ( s @ B ) ) ) ) ),
    inference(pre_uni,[status(thm)],[779:[bind(A,$thf( ^ [B: $i] : ( isIndSet @ ^ [C: $i] : ( d @ ( s @ C ) ) ) ))]]) ).

thf(811,plain,
    ( ( ! [A: $i] :
          ( ( d @ ( s @ A ) )
         => ( d @ ( s @ ( s @ A ) ) ) ) )
    = ( isIndSet
      @ ^ [A: $i] :
          ( isIndSet
          @ ^ [B: $i] : ( d @ ( s @ B ) ) ) ) ),
    inference(simp,[status(thm)],[794]) ).

thf(2219,plain,
    ( ( isIndSet
      @ ^ [A: $i] :
          ( isIndSet
          @ ^ [B: $i] : ( d @ ( s @ B ) ) ) )
    = ( isIndSet
      @ ^ [A: $i] : ( d @ ( s @ A ) ) ) ),
    inference(rewrite,[status(thm)],[268,811]) ).

thf(2485,plain,
    ( ( ! [A: $i] :
          ( ( d @ ( s @ A ) )
         => ( d @ ( s @ ( s @ A ) ) ) ) )
    = ( isIndSet
      @ ^ [A: $i] : ( d @ ( s @ A ) ) ) ),
    inference(rewrite,[status(thm)],[811,2219]) ).

thf(2858,plain,
    ( ( ( isIndSet
        @ ^ [A: $i] :
          ! [B: $i] :
            ( ( d @ ( s @ B ) )
           => ( d @ ( s @ ( s @ B ) ) ) ) )
      = ( isIndSet
        @ ^ [A: $i] : ( d @ ( s @ A ) ) ) )
    | ( ( isIndSet
        @ ^ [A: $i] : ( d @ ( s @ A ) ) )
     != ( isIndSet
        @ ^ [A: $i] : ( d @ ( s @ A ) ) ) ) ),
    inference(paramod_ordered,[status(thm)],[2485,2219]) ).

thf(2859,plain,
    ( ( isIndSet
      @ ^ [A: $i] :
        ! [B: $i] :
          ( ( d @ ( s @ B ) )
         => ( d @ ( s @ ( s @ B ) ) ) ) )
    = ( isIndSet
      @ ^ [A: $i] : ( d @ ( s @ A ) ) ) ),
    inference(pattern_uni,[status(thm)],[2858:[]]) ).

thf(3052,plain,
    ( ( ( isIndSet
        @ ^ [A: $i] :
          ! [B: $i] :
            ( ( d @ ( s @ B ) )
           => ( d @ ( s @ ( s @ B ) ) ) ) )
      = ( ! [A: $i] :
            ( ( d @ ( s @ A ) )
           => ( d @ ( s @ ( s @ A ) ) ) ) ) )
    | ( ( isIndSet
        @ ^ [A: $i] : ( d @ ( s @ A ) ) )
     != ( isIndSet
        @ ^ [A: $i] : ( d @ ( s @ A ) ) ) ) ),
    inference(paramod_ordered,[status(thm)],[2859,2485]) ).

thf(3053,plain,
    ( ( isIndSet
      @ ^ [A: $i] :
        ! [B: $i] :
          ( ( d @ ( s @ B ) )
         => ( d @ ( s @ ( s @ B ) ) ) ) )
    = ( ! [A: $i] :
          ( ( d @ ( s @ A ) )
         => ( d @ ( s @ ( s @ A ) ) ) ) ) ),
    inference(pattern_uni,[status(thm)],[3052:[]]) ).

thf(263,plain,
    ! [A: $i] :
      ( ( d @ ( s @ A ) )
      | ( ( d @ ( s @ e ) )
       != ( d @ A ) ) ),
    inference(paramod_ordered,[status(thm)],[250,22]) ).

thf(264,plain,
    d @ ( s @ ( s @ e ) ),
    inference(pattern_uni,[status(thm)],[263:[bind(A,$thf( s @ e ))]]) ).

thf(273,plain,
    ! [A: $i] :
      ( ( d @ ( s @ A ) )
      | ( ( d @ ( s @ ( s @ e ) ) )
       != ( d @ A ) ) ),
    inference(paramod_ordered,[status(thm)],[264,22]) ).

thf(274,plain,
    d @ ( s @ ( s @ ( s @ e ) ) ),
    inference(pattern_uni,[status(thm)],[273:[bind(A,$thf( s @ ( s @ e ) ))]]) ).

thf(284,plain,
    ! [A: $i] :
      ( ( d @ ( s @ A ) )
      | ( ( d @ ( s @ ( s @ ( s @ e ) ) ) )
       != ( d @ A ) ) ),
    inference(paramod_ordered,[status(thm)],[274,22]) ).

thf(285,plain,
    d @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ),
    inference(pattern_uni,[status(thm)],[284:[bind(A,$thf( s @ ( s @ ( s @ e ) ) ))]]) ).

thf(384,plain,
    ! [A: $i] :
      ( ( d @ ( s @ A ) )
      | ( ( d @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) )
       != ( d @ A ) ) ),
    inference(paramod_ordered,[status(thm)],[285,22]) ).

thf(385,plain,
    d @ ( s @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) ),
    inference(pattern_uni,[status(thm)],[384:[bind(A,$thf( s @ ( s @ ( s @ ( s @ e ) ) ) ))]]) ).

thf(399,plain,
    ! [A: $i] :
      ( ( d @ ( s @ A ) )
      | ( ( d @ ( s @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) ) )
       != ( d @ A ) ) ),
    inference(paramod_ordered,[status(thm)],[385,22]) ).

thf(400,plain,
    d @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) ) ),
    inference(pattern_uni,[status(thm)],[399:[bind(A,$thf( s @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) ))]]) ).

thf(449,plain,
    ! [A: $i] :
      ( ( d @ ( s @ A ) )
      | ( ( d @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) ) ) )
       != ( d @ A ) ) ),
    inference(paramod_ordered,[status(thm)],[400,22]) ).

thf(450,plain,
    d @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) ) ) ),
    inference(pattern_uni,[status(thm)],[449:[bind(A,$thf( s @ ( s @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) ) ))]]) ).

thf(478,plain,
    ! [A: $i] :
      ( ( d @ ( s @ A ) )
      | ( ( d @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) ) ) ) )
       != ( d @ A ) ) ),
    inference(paramod_ordered,[status(thm)],[450,22]) ).

thf(479,plain,
    d @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) ) ) ) ),
    inference(pattern_uni,[status(thm)],[478:[bind(A,$thf( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) ) ) ))]]) ).

thf(2824,plain,
    ( ~ ! [A: $i] :
          ( ( d @ ( s @ A ) )
         => ( d @ ( s @ ( s @ A ) ) ) )
    | ( ( isIndSet
        @ ^ [A: $i] : ( d @ ( s @ A ) ) )
     != ( isIndSet
        @ ^ [A: $i] : $false ) ) ),
    inference(paramod_ordered,[status(thm)],[2485,2403]) ).

thf(2884,plain,
    ( ~ ! [A: $i] :
          ( ( d @ ( s @ A ) )
         => ( d @ ( s @ ( s @ A ) ) ) )
    | ( ( ^ [A: $i] : ( d @ ( s @ A ) ) )
     != ( ^ [A: $i] : $false ) ) ),
    inference(simp,[status(thm)],[2824]) ).

thf(2921,plain,
    ( ( ( ^ [A: $i] : ( d @ ( s @ A ) ) )
     != ( ^ [A: $i] : $false ) )
    | ~ ( d @ ( s @ ( s @ sk91 ) ) ) ),
    inference(cnf,[status(esa)],[2884]) ).

thf(56,plain,
    ! [A: $i > $o] :
      ( ~ ( ( A @ e )
          & ! [B: $i] :
              ( ( A @ B )
             => ( A @ ( s @ B ) ) ) )
      | ( isIndSet @ A ) ),
    inference(bool_ext,[status(thm)],[27]) ).

thf(64,plain,
    ! [A: $i > $o] :
      ( ( isIndSet @ A )
      | ~ ( A @ e )
      | ( A @ ( sk1 @ A ) ) ),
    inference(cnf,[status(esa)],[56]) ).

thf(1299,plain,
    ! [A: $i > $o] :
      ( ( isIndSet @ A )
      | ~ ! [B: $i] :
            ( ( d @ B )
           => ( d @ ( s @ B ) ) )
      | ( A @ ( sk1 @ A ) )
      | ( ( isIndSet @ d )
       != ( A @ e ) ) ),
    inference(paramod_ordered,[status(thm)],[1044,64]) ).

thf(1354,plain,
    ( ( isIndSet
      @ ^ [A: $i] : ( isIndSet @ d ) )
    | ~ ! [A: $i] :
          ( ( d @ A )
         => ( d @ ( s @ A ) ) )
    | ( isIndSet @ d ) ),
    inference(pre_uni,[status(thm)],[1299:[bind(A,$thf( ^ [B: $i] : ( isIndSet @ d ) ))]]) ).

thf(1429,plain,
    ( ( isIndSet @ d )
    | ( d @ sk10 )
    | ( isIndSet
      @ ^ [A: $i] : ( isIndSet @ d ) ) ),
    inference(cnf,[status(esa)],[1354]) ).

thf(1085,plain,
    ( ( ( isIndSet
        @ ^ [A: $i] : ( isIndSet @ d ) )
      = ( ! [A: $i] :
            ( ( d @ A )
           => ( d @ ( s @ A ) ) ) ) )
    | ( ( ! [A: $i] :
            ( ( d @ A )
           => ( d @ ( s @ A ) ) ) )
     != ( ! [A: $i] :
            ( ( d @ A )
           => ( d @ ( s @ A ) ) ) ) ) ),
    inference(paramod_ordered,[status(thm)],[1044,112]) ).

thf(1086,plain,
    ( ( isIndSet
      @ ^ [A: $i] : ( isIndSet @ d ) )
    = ( ! [A: $i] :
          ( ( d @ A )
         => ( d @ ( s @ A ) ) ) ) ),
    inference(pattern_uni,[status(thm)],[1085:[]]) ).

thf(1118,plain,
    ( ( ( isIndSet
        @ ^ [A: $i] : ( isIndSet @ d ) )
      = ( isIndSet @ d ) )
    | ( ( ! [A: $i] :
            ( ( d @ A )
           => ( d @ ( s @ A ) ) ) )
     != ( ! [A: $i] :
            ( ( d @ A )
           => ( d @ ( s @ A ) ) ) ) ) ),
    inference(paramod_ordered,[status(thm)],[1086,1044]) ).

thf(1119,plain,
    ( ( isIndSet
      @ ^ [A: $i] : ( isIndSet @ d ) )
    = ( isIndSet @ d ) ),
    inference(pattern_uni,[status(thm)],[1118:[]]) ).

thf(31390,plain,
    ( ( isIndSet @ d )
    | ( d @ sk10 )
    | ( isIndSet @ d ) ),
    inference(rewrite,[status(thm)],[1429,1119]) ).

thf(31391,plain,
    ( ( isIndSet @ d )
    | ( d @ sk10 ) ),
    inference(simp,[status(thm)],[31390]) ).

thf(3,axiom,
    ! [A: $i] :
      ( ( f @ A @ e )
      = ( s @ e ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',a1) ).

thf(11,plain,
    ! [A: $i] :
      ( ( f @ A @ e )
      = ( s @ e ) ),
    inference(defexp_and_simp_and_etaexpand,[status(thm)],[3]) ).

thf(12,plain,
    ! [A: $i] :
      ( ( f @ A @ e )
      = ( s @ e ) ),
    inference(cnf,[status(esa)],[11]) ).

thf(13,plain,
    ! [A: $i] :
      ( ( f @ A @ e )
      = ( s @ e ) ),
    inference(lifteq,[status(thm)],[12]) ).

thf(4,axiom,
    ! [A: $i] :
      ( ( f @ e @ ( s @ A ) )
      = ( s @ ( s @ ( f @ e @ A ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',a2) ).

thf(14,plain,
    ! [A: $i] :
      ( ( f @ e @ ( s @ A ) )
      = ( s @ ( s @ ( f @ e @ A ) ) ) ),
    inference(defexp_and_simp_and_etaexpand,[status(thm)],[4]) ).

thf(15,plain,
    ! [A: $i] :
      ( ( f @ e @ ( s @ A ) )
      = ( s @ ( s @ ( f @ e @ A ) ) ) ),
    inference(cnf,[status(esa)],[14]) ).

thf(16,plain,
    ! [A: $i] :
      ( ( f @ e @ ( s @ A ) )
      = ( s @ ( s @ ( f @ e @ A ) ) ) ),
    inference(lifteq,[status(thm)],[15]) ).

thf(9,axiom,
    ( p
    = ( ^ [A: $i,B: $i] :
        ! [C: $i > $o] :
          ( ( isIndSet @ C )
         => ( C @ ( f @ A @ B ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',p_def) ).

thf(25,plain,
    ( p
    = ( ^ [A: $i,B: $i] :
        ! [C: $i > $o] :
          ( ( isIndSet @ C )
         => ( C @ ( f @ A @ B ) ) ) ) ),
    inference(defexp_and_simp_and_etaexpand,[status(thm)],[9]) ).

thf(26,plain,
    ( p
    = ( ^ [A: $i,B: $i] :
        ! [C: $i > $o] :
          ( ( isIndSet @ C )
         => ( C @ ( f @ A @ B ) ) ) ) ),
    inference(lifteq,[status(thm)],[25]) ).

thf(29,plain,
    ! [B: $i,A: $i] :
      ( ( p @ A @ B )
      = ( ! [C: $i > $o] :
            ( ( isIndSet @ C )
           => ( C @ ( f @ A @ B ) ) ) ) ),
    inference(func_ext,[status(esa)],[26]) ).

thf(366,plain,
    ! [C: $i,B: $i,A: $i] :
      ( ( ( p @ B @ C )
        = ( ! [D: $i > $o] :
              ( ( isIndSet @ D )
             => ( D @ ( s @ ( s @ ( f @ e @ A ) ) ) ) ) ) )
      | ( ( f @ e @ ( s @ A ) )
       != ( f @ B @ C ) ) ),
    inference(paramod_ordered,[status(thm)],[16,29]) ).

thf(367,plain,
    ! [A: $i] :
      ( ( p @ e @ ( s @ A ) )
      = ( ! [B: $i > $o] :
            ( ( isIndSet @ B )
           => ( B @ ( s @ ( s @ ( f @ e @ A ) ) ) ) ) ) ),
    inference(pattern_uni,[status(thm)],[366:[bind(A,$thf( D )),bind(B,$thf( e )),bind(C,$thf( s @ D ))]]) ).

thf(381,plain,
    ! [A: $i] :
      ( ( p @ e @ ( s @ A ) )
      = ( ! [B: $i > $o] :
            ( ( isIndSet @ B )
           => ( B @ ( s @ ( s @ ( f @ e @ A ) ) ) ) ) ) ),
    inference(simp,[status(thm)],[367]) ).

thf(3541,plain,
    ! [B: $i,A: $i] :
      ( ( ( p @ e @ ( s @ B ) )
        = ( ! [C: $i > $o] :
              ( ( isIndSet @ C )
             => ( C @ ( s @ ( s @ ( s @ ( s @ ( f @ e @ A ) ) ) ) ) ) ) ) )
      | ( ( f @ e @ ( s @ A ) )
       != ( f @ e @ B ) ) ),
    inference(paramod_ordered,[status(thm)],[16,381]) ).

thf(3542,plain,
    ! [A: $i] :
      ( ( p @ e @ ( s @ ( s @ A ) ) )
      = ( ! [B: $i > $o] :
            ( ( isIndSet @ B )
           => ( B @ ( s @ ( s @ ( s @ ( s @ ( f @ e @ A ) ) ) ) ) ) ) ) ),
    inference(pattern_uni,[status(thm)],[3541:[bind(A,$thf( C )),bind(B,$thf( s @ C ))]]) ).

thf(3570,plain,
    ! [A: $i] :
      ( ( p @ e @ ( s @ ( s @ A ) ) )
      = ( ! [B: $i > $o] :
            ( ( isIndSet @ B )
           => ( B @ ( s @ ( s @ ( s @ ( s @ ( f @ e @ A ) ) ) ) ) ) ) ) ),
    inference(simp,[status(thm)],[3542]) ).

thf(7284,plain,
    ! [B: $i,A: $i] :
      ( ( ( p @ e @ ( s @ ( s @ B ) ) )
        = ( ! [C: $i > $o] :
              ( ( isIndSet @ C )
             => ( C @ ( s @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) ) ) ) ) )
      | ( ( f @ A @ e )
       != ( f @ e @ B ) ) ),
    inference(paramod_ordered,[status(thm)],[13,3570]) ).

thf(7285,plain,
    ( ( p @ e @ ( s @ ( s @ e ) ) )
    = ( ! [A: $i > $o] :
          ( ( isIndSet @ A )
         => ( A @ ( s @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) ) ) ) ) ),
    inference(pattern_uni,[status(thm)],[7284:[bind(A,$thf( e )),bind(B,$thf( e ))]]) ).

thf(3115,plain,
    ( ( ( isIndSet
        @ ^ [A: $i] :
            ( isIndSet
            @ ^ [B: $i] :
              ! [C: $i] :
                ( ( d @ ( s @ C ) )
               => ( d @ ( s @ ( s @ C ) ) ) ) ) )
      = ( isIndSet
        @ ^ [A: $i] : ( d @ ( s @ A ) ) ) )
    | ( ( isIndSet
        @ ^ [A: $i] : ( d @ ( s @ A ) ) )
     != ( isIndSet
        @ ^ [A: $i] : ( d @ ( s @ A ) ) ) ) ),
    inference(paramod_ordered,[status(thm)],[2859,2219]) ).

thf(3116,plain,
    ( ( isIndSet
      @ ^ [A: $i] :
          ( isIndSet
          @ ^ [B: $i] :
            ! [C: $i] :
              ( ( d @ ( s @ C ) )
             => ( d @ ( s @ ( s @ C ) ) ) ) ) )
    = ( isIndSet
      @ ^ [A: $i] : ( d @ ( s @ A ) ) ) ),
    inference(pattern_uni,[status(thm)],[3115:[]]) ).

thf(3362,plain,
    ( ( ( isIndSet
        @ ^ [A: $i] :
            ( isIndSet
            @ ^ [B: $i] :
                ( isIndSet
                @ ^ [C: $i] :
                  ! [D: $i] :
                    ( ( d @ ( s @ D ) )
                   => ( d @ ( s @ ( s @ D ) ) ) ) ) ) )
      = ( isIndSet
        @ ^ [A: $i] : ( d @ ( s @ A ) ) ) )
    | ( ( isIndSet
        @ ^ [A: $i] : ( d @ ( s @ A ) ) )
     != ( isIndSet
        @ ^ [A: $i] : ( d @ ( s @ A ) ) ) ) ),
    inference(paramod_ordered,[status(thm)],[3116,2219]) ).

thf(3363,plain,
    ( ( isIndSet
      @ ^ [A: $i] :
          ( isIndSet
          @ ^ [B: $i] :
              ( isIndSet
              @ ^ [C: $i] :
                ! [D: $i] :
                  ( ( d @ ( s @ D ) )
                 => ( d @ ( s @ ( s @ D ) ) ) ) ) ) )
    = ( isIndSet
      @ ^ [A: $i] : ( d @ ( s @ A ) ) ) ),
    inference(pattern_uni,[status(thm)],[3362:[]]) ).

thf(5645,plain,
    ( ( ( isIndSet
        @ ^ [A: $i] :
            ( isIndSet
            @ ^ [B: $i] :
                ( isIndSet
                @ ^ [C: $i] :
                    ( isIndSet
                    @ ^ [D: $i] : ( d @ ( s @ D ) ) ) ) ) )
      = ( isIndSet
        @ ^ [A: $i] : ( d @ ( s @ A ) ) ) )
    | ( ( ! [A: $i] :
            ( ( d @ ( s @ A ) )
           => ( d @ ( s @ ( s @ A ) ) ) ) )
     != ( ! [A: $i] :
            ( ( d @ ( s @ A ) )
           => ( d @ ( s @ ( s @ A ) ) ) ) ) ) ),
    inference(paramod_ordered,[status(thm)],[2485,3363]) ).

thf(5646,plain,
    ( ( isIndSet
      @ ^ [A: $i] :
          ( isIndSet
          @ ^ [B: $i] :
              ( isIndSet
              @ ^ [C: $i] :
                  ( isIndSet
                  @ ^ [D: $i] : ( d @ ( s @ D ) ) ) ) ) )
    = ( isIndSet
      @ ^ [A: $i] : ( d @ ( s @ A ) ) ) ),
    inference(pattern_uni,[status(thm)],[5645:[]]) ).

thf(5793,plain,
    ( ( isIndSet
      @ ^ [A: $i] :
          ( isIndSet
          @ ^ [B: $i] :
              ( isIndSet
              @ ^ [C: $i] : ( d @ ( s @ C ) ) ) ) )
    = ( isIndSet
      @ ^ [A: $i] : ( d @ ( s @ A ) ) ) ),
    inference(rewrite,[status(thm)],[5646,2219]) ).

thf(275,plain,
    ! [A: $i > $o] :
      ( ( ( ! [B: $i] :
              ( ( A @ B )
             => ( A @ ( s @ B ) ) ) )
        = ( isIndSet @ A ) )
      | ( ( d @ ( s @ ( s @ e ) ) )
       != ( A @ e ) ) ),
    inference(paramod_ordered,[status(thm)],[264,27]) ).

thf(279,plain,
    ( ( ! [A: $i] :
          ( ( d @ ( s @ ( s @ A ) ) )
         => ( d @ ( s @ ( s @ ( s @ A ) ) ) ) ) )
    = ( isIndSet
      @ ^ [A: $i] : ( d @ ( s @ ( s @ A ) ) ) ) ),
    inference(pre_uni,[status(thm)],[275:[bind(A,$thf( ^ [B: $i] : ( d @ ( s @ ( s @ B ) ) ) ))]]) ).

thf(4323,plain,
    ! [A: $i > $o] :
      ( ( ( ! [B: $i] :
              ( ( d @ ( s @ ( s @ B ) ) )
             => ( d @ ( s @ ( s @ ( s @ B ) ) ) ) )
          & ! [B: $i] :
              ( ( A @ B )
             => ( A @ ( s @ B ) ) ) )
        = ( isIndSet @ A ) )
      | ( ( isIndSet
          @ ^ [B: $i] : ( d @ ( s @ ( s @ B ) ) ) )
       != ( A @ e ) ) ),
    inference(paramod_ordered,[status(thm)],[279,27]) ).

thf(4379,plain,
    ( ( ! [A: $i] :
          ( ( d @ ( s @ ( s @ A ) ) )
         => ( d @ ( s @ ( s @ ( s @ A ) ) ) ) )
      & ! [A: $i] :
          ( ( isIndSet
            @ ^ [B: $i] : ( d @ ( s @ ( s @ B ) ) ) )
         => ( isIndSet
            @ ^ [B: $i] : ( d @ ( s @ ( s @ B ) ) ) ) ) )
    = ( isIndSet
      @ ^ [A: $i] :
          ( isIndSet
          @ ^ [B: $i] : ( d @ ( s @ ( s @ B ) ) ) ) ) ),
    inference(pre_uni,[status(thm)],[4323:[bind(A,$thf( ^ [B: $i] : ( isIndSet @ ^ [C: $i] : ( d @ ( s @ ( s @ C ) ) ) ) ))]]) ).

thf(4438,plain,
    ( ( ! [A: $i] :
          ( ( d @ ( s @ ( s @ A ) ) )
         => ( d @ ( s @ ( s @ ( s @ A ) ) ) ) ) )
    = ( isIndSet
      @ ^ [A: $i] :
          ( isIndSet
          @ ^ [B: $i] : ( d @ ( s @ ( s @ B ) ) ) ) ) ),
    inference(simp,[status(thm)],[4379]) ).

thf(9631,plain,
    ( ( isIndSet
      @ ^ [A: $i] :
          ( isIndSet
          @ ^ [B: $i] : ( d @ ( s @ ( s @ B ) ) ) ) )
    = ( isIndSet
      @ ^ [A: $i] : ( d @ ( s @ ( s @ A ) ) ) ) ),
    inference(rewrite,[status(thm)],[279,4438]) ).

thf(9686,plain,
    ( ( ! [A: $i] :
          ( ( d @ ( s @ ( s @ A ) ) )
         => ( d @ ( s @ ( s @ ( s @ A ) ) ) ) ) )
    = ( isIndSet
      @ ^ [A: $i] : ( d @ ( s @ ( s @ A ) ) ) ) ),
    inference(rewrite,[status(thm)],[4438,9631]) ).

thf(10313,plain,
    ( ( ( isIndSet
        @ ^ [A: $i] :
          ! [B: $i] :
            ( ( d @ ( s @ ( s @ B ) ) )
           => ( d @ ( s @ ( s @ ( s @ B ) ) ) ) ) )
      = ( isIndSet
        @ ^ [A: $i] : ( d @ ( s @ ( s @ A ) ) ) ) )
    | ( ( isIndSet
        @ ^ [A: $i] : ( d @ ( s @ ( s @ A ) ) ) )
     != ( isIndSet
        @ ^ [A: $i] : ( d @ ( s @ ( s @ A ) ) ) ) ) ),
    inference(paramod_ordered,[status(thm)],[9686,9631]) ).

thf(10314,plain,
    ( ( isIndSet
      @ ^ [A: $i] :
        ! [B: $i] :
          ( ( d @ ( s @ ( s @ B ) ) )
         => ( d @ ( s @ ( s @ ( s @ B ) ) ) ) ) )
    = ( isIndSet
      @ ^ [A: $i] : ( d @ ( s @ ( s @ A ) ) ) ) ),
    inference(pattern_uni,[status(thm)],[10313:[]]) ).

thf(25383,plain,
    ! [A: $i] :
      ( ~ ( d @ A )
      | ( ( ^ [B: $i] : ( d @ ( s @ B ) ) )
       != ( ^ [B: $i] : $false ) )
      | ( ( d @ ( s @ A ) )
       != ( d @ ( s @ ( s @ sk91 ) ) ) ) ),
    inference(paramod_ordered,[status(thm)],[22,2921]) ).

thf(25384,plain,
    ( ~ ( d @ ( s @ sk91 ) )
    | ( ( ^ [A: $i] : ( d @ ( s @ A ) ) )
     != ( ^ [A: $i] : $false ) ) ),
    inference(pattern_uni,[status(thm)],[25383:[bind(A,$thf( s @ sk91 ))]]) ).

thf(25450,plain,
    ( ( ( ^ [A: $i] : ( d @ ( s @ A ) ) )
     != ( ^ [A: $i] : $false ) )
    | ( ( d @ ( s @ sk91 ) )
     != ( d @ e ) ) ),
    inference(paramod_ordered,[status(thm)],[20,25384]) ).

thf(25494,plain,
    ( ( ( ^ [A: $i] : ( d @ ( s @ A ) ) )
     != ( ^ [A: $i] : $false ) )
    | ( ( s @ sk91 )
     != e ) ),
    inference(simp,[status(thm)],[25450]) ).

thf(7356,plain,
    ! [B: $i,A: $i] :
      ( ( ( p @ e @ ( s @ ( s @ B ) ) )
        = ( ! [C: $i > $o] :
              ( ( isIndSet @ C )
             => ( C @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( f @ e @ A ) ) ) ) ) ) ) ) ) ) )
      | ( ( f @ e @ ( s @ A ) )
       != ( f @ e @ B ) ) ),
    inference(paramod_ordered,[status(thm)],[16,3570]) ).

thf(7357,plain,
    ! [A: $i] :
      ( ( p @ e @ ( s @ ( s @ ( s @ A ) ) ) )
      = ( ! [B: $i > $o] :
            ( ( isIndSet @ B )
           => ( B @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( f @ e @ A ) ) ) ) ) ) ) ) ) ) ),
    inference(pattern_uni,[status(thm)],[7356:[bind(A,$thf( C )),bind(B,$thf( s @ C ))]]) ).

thf(7433,plain,
    ! [A: $i] :
      ( ( p @ e @ ( s @ ( s @ ( s @ A ) ) ) )
      = ( ! [B: $i > $o] :
            ( ( isIndSet @ B )
           => ( B @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( f @ e @ A ) ) ) ) ) ) ) ) ) ) ),
    inference(simp,[status(thm)],[7357]) ).

thf(11986,plain,
    ! [B: $i,A: $i] :
      ( ( ( p @ e @ ( s @ ( s @ ( s @ B ) ) ) )
        = ( ! [C: $i > $o] :
              ( ( isIndSet @ C )
             => ( C @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( f @ e @ A ) ) ) ) ) ) ) ) ) ) ) ) )
      | ( ( f @ e @ ( s @ A ) )
       != ( f @ e @ B ) ) ),
    inference(paramod_ordered,[status(thm)],[16,7433]) ).

thf(11987,plain,
    ! [A: $i] :
      ( ( p @ e @ ( s @ ( s @ ( s @ ( s @ A ) ) ) ) )
      = ( ! [B: $i > $o] :
            ( ( isIndSet @ B )
           => ( B @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( f @ e @ A ) ) ) ) ) ) ) ) ) ) ) ) ),
    inference(pattern_uni,[status(thm)],[11986:[bind(A,$thf( C )),bind(B,$thf( s @ C ))]]) ).

thf(12179,plain,
    ! [A: $i] :
      ( ( p @ e @ ( s @ ( s @ ( s @ ( s @ A ) ) ) ) )
      = ( ! [B: $i > $o] :
            ( ( isIndSet @ B )
           => ( B @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( f @ e @ A ) ) ) ) ) ) ) ) ) ) ) ) ),
    inference(simp,[status(thm)],[11987]) ).

thf(19854,plain,
    ! [C: $i,B: $i,A: $i] :
      ( ( ( ! [D: $i > $o] :
              ( ( isIndSet @ D )
             => ( D @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( f @ e @ A ) ) ) ) ) ) ) ) ) ) ) )
        = ( ! [D: $i > $o] :
              ( ( isIndSet @ D )
             => ( D @ ( f @ B @ C ) ) ) ) )
      | ( ( p @ e @ ( s @ ( s @ ( s @ ( s @ A ) ) ) ) )
       != ( p @ B @ C ) ) ),
    inference(paramod_ordered,[status(thm)],[12179,29]) ).

thf(19855,plain,
    ! [A: $i] :
      ( ( ! [B: $i > $o] :
            ( ( isIndSet @ B )
           => ( B @ ( f @ e @ ( s @ ( s @ ( s @ ( s @ A ) ) ) ) ) ) ) )
      = ( ! [B: $i > $o] :
            ( ( isIndSet @ B )
           => ( B @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( f @ e @ A ) ) ) ) ) ) ) ) ) ) ) ) ),
    inference(pattern_uni,[status(thm)],[19854:[bind(A,$thf( G )),bind(B,$thf( e )),bind(C,$thf( s @ ( s @ ( s @ ( s @ G ) ) ) ))]]) ).

thf(20217,plain,
    ! [A: $i] :
      ( ( ! [B: $i > $o] :
            ( ( isIndSet @ B )
           => ( B @ ( f @ e @ ( s @ ( s @ ( s @ ( s @ A ) ) ) ) ) ) ) )
      = ( ! [B: $i > $o] :
            ( ( isIndSet @ B )
           => ( B @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( f @ e @ A ) ) ) ) ) ) ) ) ) ) ) ) ),
    inference(simp,[status(thm)],[19855]) ).

thf(24995,plain,
    ! [A: $i] :
      ( ( ! [B: $i > $o] :
            ( ( isIndSet @ B )
           => ( B @ ( s @ ( s @ ( f @ e @ ( s @ ( s @ ( s @ A ) ) ) ) ) ) ) ) )
      = ( ! [B: $i > $o] :
            ( ( isIndSet @ B )
           => ( B @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( f @ e @ A ) ) ) ) ) ) ) ) ) ) ) ) ),
    inference(rewrite,[status(thm)],[20217,16]) ).

thf(1,conjecture,
    d @ ( f @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',conj_0) ).

thf(2,negated_conjecture,
    ~ ( d @ ( f @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) ) ),
    inference(neg_conjecture,[status(cth)],[1]) ).

thf(10,plain,
    ~ ( d @ ( f @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) ) ),
    inference(defexp_and_simp_and_etaexpand,[status(thm)],[2]) ).

thf(3493,plain,
    ! [B: $i,A: $i] :
      ( ( ( p @ e @ ( s @ B ) )
        = ( ! [C: $i > $o] :
              ( ( isIndSet @ C )
             => ( C @ ( s @ ( s @ ( s @ e ) ) ) ) ) ) )
      | ( ( f @ A @ e )
       != ( f @ e @ B ) ) ),
    inference(paramod_ordered,[status(thm)],[13,381]) ).

thf(3494,plain,
    ( ( p @ e @ ( s @ e ) )
    = ( ! [A: $i > $o] :
          ( ( isIndSet @ A )
         => ( A @ ( s @ ( s @ ( s @ e ) ) ) ) ) ) ),
    inference(pattern_uni,[status(thm)],[3493:[bind(A,$thf( e )),bind(B,$thf( e ))]]) ).

thf(3653,plain,
    ! [A: $i > $o] :
      ( ( ( ! [B: $i > $o] :
              ( ( isIndSet @ B )
             => ( B @ ( s @ ( s @ ( s @ e ) ) ) ) )
          & ! [B: $i] :
              ( ( A @ B )
             => ( A @ ( s @ B ) ) ) )
        = ( isIndSet @ A ) )
      | ( ( p @ e @ ( s @ e ) )
       != ( A @ e ) ) ),
    inference(paramod_ordered,[status(thm)],[3494,27]) ).

thf(3661,plain,
    ( ( ! [A: $i > $o] :
          ( ( isIndSet @ A )
         => ( A @ ( s @ ( s @ ( s @ e ) ) ) ) )
      & ! [A: $i] :
          ( ( p @ A @ ( s @ A ) )
         => ( p @ ( s @ A ) @ ( s @ ( s @ A ) ) ) ) )
    = ( isIndSet
      @ ^ [A: $i] : ( p @ A @ ( s @ A ) ) ) ),
    inference(pre_uni,[status(thm)],[3653:[bind(A,$thf( ^ [B: $i] : ( p @ B @ ( s @ B ) ) ))]]) ).

thf(16802,plain,
    ! [A: $i > $o] :
      ( ( ( ! [B: $i > $o] :
              ( ( isIndSet @ B )
             => ( B @ ( s @ ( s @ ( s @ e ) ) ) ) )
          & ! [B: $i] :
              ( ( p @ B @ ( s @ B ) )
             => ( p @ ( s @ B ) @ ( s @ ( s @ B ) ) ) )
          & ! [B: $i] :
              ( ( A @ B )
             => ( A @ ( s @ B ) ) ) )
        = ( isIndSet @ A ) )
      | ( ( isIndSet
          @ ^ [B: $i] : ( p @ B @ ( s @ B ) ) )
       != ( A @ e ) ) ),
    inference(paramod_ordered,[status(thm)],[3661,27]) ).

thf(16993,plain,
    ( ( ! [A: $i > $o] :
          ( ( isIndSet @ A )
         => ( A @ ( s @ ( s @ ( s @ e ) ) ) ) )
      & ! [A: $i] :
          ( ( p @ A @ ( s @ A ) )
         => ( p @ ( s @ A ) @ ( s @ ( s @ A ) ) ) )
      & ! [A: $i] :
          ( ( isIndSet
            @ ^ [B: $i] : ( p @ B @ ( s @ B ) ) )
         => ( isIndSet
            @ ^ [B: $i] : ( p @ B @ ( s @ B ) ) ) ) )
    = ( isIndSet
      @ ^ [A: $i] :
          ( isIndSet
          @ ^ [B: $i] : ( p @ B @ ( s @ B ) ) ) ) ),
    inference(pre_uni,[status(thm)],[16802:[bind(A,$thf( ^ [B: $i] : ( isIndSet @ ^ [C: $i] : ( p @ C @ ( s @ C ) ) ) ))]]) ).

thf(17144,plain,
    ( ( ! [A: $i > $o] :
          ( ( isIndSet @ A )
         => ( A @ ( s @ ( s @ ( s @ e ) ) ) ) )
      & ! [A: $i] :
          ( ( p @ A @ ( s @ A ) )
         => ( p @ ( s @ A ) @ ( s @ ( s @ A ) ) ) ) )
    = ( isIndSet
      @ ^ [A: $i] :
          ( isIndSet
          @ ^ [B: $i] : ( p @ B @ ( s @ B ) ) ) ) ),
    inference(simp,[status(thm)],[16993]) ).

thf(28317,plain,
    ( ( isIndSet
      @ ^ [A: $i] :
          ( isIndSet
          @ ^ [B: $i] : ( p @ B @ ( s @ B ) ) ) )
    = ( isIndSet
      @ ^ [A: $i] : ( p @ A @ ( s @ A ) ) ) ),
    inference(rewrite,[status(thm)],[3661,17144]) ).

thf(79,plain,
    ( ~ ! [A: $i] :
          ( ( d @ A )
         => ( d @ ( s @ A ) ) )
    | ( isIndSet @ d ) ),
    inference(bool_ext,[status(thm)],[61]) ).

thf(96,plain,
    ( ( isIndSet @ d )
    | ~ ( d @ ( s @ sk2 ) ) ),
    inference(cnf,[status(esa)],[79]) ).

thf(2445,plain,
    ( ~ ( isIndSet @ d )
    | ( ( isIndSet
        @ ^ [A: $i] : ( isIndSet @ d ) )
     != ( isIndSet
        @ ^ [A: $i] : $false ) ) ),
    inference(paramod_ordered,[status(thm)],[1119,2403]) ).

thf(2464,plain,
    ( ~ ( isIndSet @ d )
    | ( ( ^ [A: $i] : ( isIndSet @ d ) )
     != ( ^ [A: $i] : $false ) ) ),
    inference(simp,[status(thm)],[2445]) ).

thf(4017,plain,
    ( ~ ( d @ ( s @ sk2 ) )
    | ( ( ^ [A: $i] : ( isIndSet @ d ) )
     != ( ^ [A: $i] : $false ) )
    | ( ( isIndSet @ d )
     != ( isIndSet @ d ) ) ),
    inference(paramod_ordered,[status(thm)],[96,2464]) ).

thf(4018,plain,
    ( ~ ( d @ ( s @ sk2 ) )
    | ( ( ^ [A: $i] : ( isIndSet @ d ) )
     != ( ^ [A: $i] : $false ) ) ),
    inference(pattern_uni,[status(thm)],[4017:[]]) ).

thf(12926,plain,
    ! [A: $i] :
      ( ~ ( d @ A )
      | ( ( ^ [B: $i] : ( isIndSet @ d ) )
       != ( ^ [B: $i] : $false ) )
      | ( ( d @ ( s @ A ) )
       != ( d @ ( s @ sk2 ) ) ) ),
    inference(paramod_ordered,[status(thm)],[22,4018]) ).

thf(12927,plain,
    ( ~ ( d @ sk2 )
    | ( ( ^ [A: $i] : ( isIndSet @ d ) )
     != ( ^ [A: $i] : $false ) ) ),
    inference(pattern_uni,[status(thm)],[12926:[bind(A,$thf( sk2 ))]]) ).

thf(13064,plain,
    ! [A: $i > $o] :
      ( ~ ( isIndSet @ A )
      | ( ( ^ [B: $i] : ( isIndSet @ d ) )
       != ( ^ [B: $i] : $false ) )
      | ( ( A @ e )
       != ( d @ sk2 ) ) ),
    inference(paramod_ordered,[status(thm)],[67,12927]) ).

thf(13115,plain,
    ( ~ ( isIndSet
        @ ^ [A: $i] : ( d @ sk2 ) )
    | ( ( ^ [A: $i] : ( isIndSet @ d ) )
     != ( ^ [A: $i] : $false ) ) ),
    inference(pre_uni,[status(thm)],[13064:[bind(A,$thf( ^ [B: $i] : ( d @ sk2 ) ))]]) ).

thf(3465,plain,
    ( ( d
     != ( ^ [A: $i] : $false ) )
    | ( ( d @ ( s @ ( s @ ( s @ e ) ) ) )
     != ( d @ sk69 ) ) ),
    inference(paramod_ordered,[status(thm)],[274,2989]) ).

thf(3481,plain,
    ( ( d
     != ( ^ [A: $i] : $false ) )
    | ( ( s @ ( s @ ( s @ e ) ) )
     != sk69 ) ),
    inference(simp,[status(thm)],[3465]) ).

thf(1304,plain,
    ! [A: $i > $o] :
      ( ( isIndSet @ A )
      | ( A @ ( sk1 @ A ) )
      | ( ( d @ e )
       != ( A @ e ) ) ),
    inference(paramod_ordered,[status(thm)],[20,64]) ).

thf(1391,plain,
    ( ( isIndSet @ d )
    | ( d @ ( sk1 @ d ) ) ),
    inference(pre_uni,[status(thm)],[1304:[bind(A,$thf( d ))]]) ).

thf(11889,plain,
    ! [B: $i,A: $i] :
      ( ( ( ! [C: $i > $o] :
              ( ( isIndSet @ C )
             => ( C @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( f @ e @ A ) ) ) ) ) ) ) ) ) )
        = ( ! [C: $i > $o] :
              ( ( isIndSet @ C )
             => ( C @ ( s @ ( s @ ( f @ e @ B ) ) ) ) ) ) )
      | ( ( p @ e @ ( s @ ( s @ ( s @ A ) ) ) )
       != ( p @ e @ ( s @ B ) ) ) ),
    inference(paramod_ordered,[status(thm)],[7433,381]) ).

thf(11890,plain,
    ! [A: $i] :
      ( ( ! [B: $i > $o] :
            ( ( isIndSet @ B )
           => ( B @ ( s @ ( s @ ( f @ e @ ( s @ ( s @ A ) ) ) ) ) ) ) )
      = ( ! [B: $i > $o] :
            ( ( isIndSet @ B )
           => ( B @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( f @ e @ A ) ) ) ) ) ) ) ) ) ) ),
    inference(pattern_uni,[status(thm)],[11889:[bind(A,$thf( D )),bind(B,$thf( s @ ( s @ D ) ))]]) ).

thf(12166,plain,
    ! [A: $i] :
      ( ( ! [B: $i > $o] :
            ( ( isIndSet @ B )
           => ( B @ ( s @ ( s @ ( f @ e @ ( s @ ( s @ A ) ) ) ) ) ) ) )
      = ( ! [B: $i > $o] :
            ( ( isIndSet @ B )
           => ( B @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( f @ e @ A ) ) ) ) ) ) ) ) ) ) ),
    inference(simp,[status(thm)],[11890]) ).

thf(7298,plain,
    ! [C: $i,B: $i,A: $i] :
      ( ( ( ! [D: $i > $o] :
              ( ( isIndSet @ D )
             => ( D @ ( s @ ( s @ ( s @ ( s @ ( f @ e @ A ) ) ) ) ) ) ) )
        = ( ! [D: $i > $o] :
              ( ( isIndSet @ D )
             => ( D @ ( f @ B @ C ) ) ) ) )
      | ( ( p @ e @ ( s @ ( s @ A ) ) )
       != ( p @ B @ C ) ) ),
    inference(paramod_ordered,[status(thm)],[3570,29]) ).

thf(7299,plain,
    ! [A: $i] :
      ( ( ! [B: $i > $o] :
            ( ( isIndSet @ B )
           => ( B @ ( f @ e @ ( s @ ( s @ A ) ) ) ) ) )
      = ( ! [B: $i > $o] :
            ( ( isIndSet @ B )
           => ( B @ ( s @ ( s @ ( s @ ( s @ ( f @ e @ A ) ) ) ) ) ) ) ) ),
    inference(pattern_uni,[status(thm)],[7298:[bind(A,$thf( E )),bind(B,$thf( e )),bind(C,$thf( s @ ( s @ E ) ))]]) ).

thf(7426,plain,
    ! [A: $i] :
      ( ( ! [B: $i > $o] :
            ( ( isIndSet @ B )
           => ( B @ ( f @ e @ ( s @ ( s @ A ) ) ) ) ) )
      = ( ! [B: $i > $o] :
            ( ( isIndSet @ B )
           => ( B @ ( s @ ( s @ ( s @ ( s @ ( f @ e @ A ) ) ) ) ) ) ) ) ),
    inference(simp,[status(thm)],[7299]) ).

thf(9281,plain,
    ! [A: $i] :
      ( ( ! [B: $i > $o] :
            ( ( isIndSet @ B )
           => ( B @ ( s @ ( s @ ( f @ e @ ( s @ A ) ) ) ) ) ) )
      = ( ! [B: $i > $o] :
            ( ( isIndSet @ B )
           => ( B @ ( s @ ( s @ ( s @ ( s @ ( f @ e @ A ) ) ) ) ) ) ) ) ),
    inference(rewrite,[status(thm)],[7426,16]) ).

thf(13552,plain,
    ! [A: $i] :
      ( ( ! [B: $i > $o] :
            ( ( isIndSet @ B )
           => ( B @ ( s @ ( s @ ( s @ ( s @ ( f @ e @ ( s @ A ) ) ) ) ) ) ) ) )
      = ( ! [B: $i > $o] :
            ( ( isIndSet @ B )
           => ( B @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( f @ e @ A ) ) ) ) ) ) ) ) ) ) ),
    inference(rewrite,[status(thm)],[12166,9281]) ).

thf(4013,plain,
    ( ~ ( d @ ( s @ sk2 ) )
    | ( ( isIndSet @ d )
     != ( isIndSet
        @ ^ [A: $i] : $false ) ) ),
    inference(paramod_ordered,[status(thm)],[96,2403]) ).

thf(4091,plain,
    ( ~ ( d @ ( s @ sk2 ) )
    | ( d
     != ( ^ [A: $i] : $false ) ) ),
    inference(simp,[status(thm)],[4013]) ).

thf(4505,plain,
    ( ( d
     != ( ^ [A: $i] : $false ) )
    | ( ( d @ ( s @ sk2 ) )
     != ( d @ e ) ) ),
    inference(paramod_ordered,[status(thm)],[20,4091]) ).

thf(4524,plain,
    ( ( d
     != ( ^ [A: $i] : $false ) )
    | ( ( s @ sk2 )
     != e ) ),
    inference(simp,[status(thm)],[4505]) ).

thf(1137,plain,
    ( ( ( isIndSet
        @ ^ [A: $i] :
            ( isIndSet
            @ ^ [B: $i] : ( isIndSet @ d ) ) )
      = ( ! [A: $i] :
            ( ( d @ A )
           => ( d @ ( s @ A ) ) ) ) )
    | ( ( ! [A: $i] :
            ( ( d @ A )
           => ( d @ ( s @ A ) ) ) )
     != ( ! [A: $i] :
            ( ( d @ A )
           => ( d @ ( s @ A ) ) ) ) ) ),
    inference(paramod_ordered,[status(thm)],[1086,112]) ).

thf(1138,plain,
    ( ( isIndSet
      @ ^ [A: $i] :
          ( isIndSet
          @ ^ [B: $i] : ( isIndSet @ d ) ) )
    = ( ! [A: $i] :
          ( ( d @ A )
         => ( d @ ( s @ A ) ) ) ) ),
    inference(pattern_uni,[status(thm)],[1137:[]]) ).

thf(1491,plain,
    ( ( isIndSet
      @ ^ [A: $i] : ( isIndSet @ d ) )
    = ( ! [A: $i] :
          ( ( d @ A )
         => ( d @ ( s @ A ) ) ) ) ),
    inference(rewrite,[status(thm)],[1138,1119]) ).

thf(2449,plain,
    ( ~ ! [A: $i] :
          ( ( d @ A )
         => ( d @ ( s @ A ) ) )
    | ( ( isIndSet
        @ ^ [A: $i] : ( isIndSet @ d ) )
     != ( isIndSet
        @ ^ [A: $i] : $false ) ) ),
    inference(paramod_ordered,[status(thm)],[1491,2403]) ).

thf(2468,plain,
    ( ~ ! [A: $i] :
          ( ( d @ A )
         => ( d @ ( s @ A ) ) )
    | ( ( ^ [A: $i] : ( isIndSet @ d ) )
     != ( ^ [A: $i] : $false ) ) ),
    inference(simp,[status(thm)],[2449]) ).

thf(2479,plain,
    ( ( ( ^ [A: $i] : ( isIndSet @ d ) )
     != ( ^ [A: $i] : $false ) )
    | ~ ( d @ ( s @ sk68 ) ) ),
    inference(cnf,[status(esa)],[2468]) ).

thf(8836,plain,
    ! [A: $i] :
      ( ~ ( d @ A )
      | ( ( ^ [B: $i] : ( isIndSet @ d ) )
       != ( ^ [B: $i] : $false ) )
      | ( ( d @ ( s @ A ) )
       != ( d @ ( s @ sk68 ) ) ) ),
    inference(paramod_ordered,[status(thm)],[22,2479]) ).

thf(8837,plain,
    ( ~ ( d @ sk68 )
    | ( ( ^ [A: $i] : ( isIndSet @ d ) )
     != ( ^ [A: $i] : $false ) ) ),
    inference(pattern_uni,[status(thm)],[8836:[bind(A,$thf( sk68 ))]]) ).

thf(8917,plain,
    ( ( ( ^ [A: $i] : ( isIndSet @ d ) )
     != ( ^ [A: $i] : $false ) )
    | ( ( d @ sk68 )
     != ( d @ e ) ) ),
    inference(paramod_ordered,[status(thm)],[20,8837]) ).

thf(8967,plain,
    ( ( ( ^ [A: $i] : ( isIndSet @ d ) )
     != ( ^ [A: $i] : $false ) )
    | ( sk68 != e ) ),
    inference(simp,[status(thm)],[8917]) ).

thf(28448,plain,
    ( ( ! [A: $i > $o] :
          ( ( isIndSet @ A )
         => ( A @ ( s @ ( s @ ( s @ e ) ) ) ) )
      & ! [A: $i] :
          ( ( p @ A @ ( s @ A ) )
         => ( p @ ( s @ A ) @ ( s @ ( s @ A ) ) ) ) )
    = ( isIndSet
      @ ^ [A: $i] : ( p @ A @ ( s @ A ) ) ) ),
    inference(rewrite,[status(thm)],[17144,28317]) ).

thf(2592,plain,
    ( ~ ! [A: $i] :
          ( ( d @ A )
         => ( d @ ( s @ A ) ) )
    | ( ( ^ [A: $i] : ( isIndSet @ d ) )
     != ( ^ [A: $i] : $false ) )
    | ( ( isIndSet @ d )
     != ( isIndSet @ d ) ) ),
    inference(paramod_ordered,[status(thm)],[1044,2464]) ).

thf(2593,plain,
    ( ~ ! [A: $i] :
          ( ( d @ A )
         => ( d @ ( s @ A ) ) )
    | ( ( ^ [A: $i] : ( isIndSet @ d ) )
     != ( ^ [A: $i] : $false ) ) ),
    inference(pattern_uni,[status(thm)],[2592:[]]) ).

thf(2629,plain,
    ( ( ( ^ [A: $i] : ( isIndSet @ d ) )
     != ( ^ [A: $i] : $false ) )
    | ~ ( d @ ( s @ sk71 ) ) ),
    inference(cnf,[status(esa)],[2593]) ).

thf(9929,plain,
    ! [A: $i] :
      ( ~ ( d @ A )
      | ( ( ^ [B: $i] : ( isIndSet @ d ) )
       != ( ^ [B: $i] : $false ) )
      | ( ( d @ ( s @ A ) )
       != ( d @ ( s @ sk71 ) ) ) ),
    inference(paramod_ordered,[status(thm)],[22,2629]) ).

thf(9930,plain,
    ( ~ ( d @ sk71 )
    | ( ( ^ [A: $i] : ( isIndSet @ d ) )
     != ( ^ [A: $i] : $false ) ) ),
    inference(pattern_uni,[status(thm)],[9929:[bind(A,$thf( sk71 ))]]) ).

thf(10037,plain,
    ! [A: $i > $o] :
      ( ~ ( isIndSet @ A )
      | ( ( ^ [B: $i] : ( isIndSet @ d ) )
       != ( ^ [B: $i] : $false ) )
      | ( ( A @ e )
       != ( d @ sk71 ) ) ),
    inference(paramod_ordered,[status(thm)],[67,9930]) ).

thf(10074,plain,
    ( ~ ( isIndSet
        @ ^ [A: $i] : ( d @ sk71 ) )
    | ( ( ^ [A: $i] : ( isIndSet @ d ) )
     != ( ^ [A: $i] : $false ) ) ),
    inference(pre_uni,[status(thm)],[10037:[bind(A,$thf( ^ [B: $i] : ( d @ sk71 ) ))]]) ).

thf(7858,plain,
    ! [A: $i > $o] :
      ( ( ( ! [B: $i > $o] :
              ( ( isIndSet @ B )
             => ( B @ ( s @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) ) ) )
          & ! [B: $i] :
              ( ( A @ B )
             => ( A @ ( s @ B ) ) ) )
        = ( isIndSet @ A ) )
      | ( ( p @ e @ ( s @ ( s @ e ) ) )
       != ( A @ e ) ) ),
    inference(paramod_ordered,[status(thm)],[7285,27]) ).

thf(7913,plain,
    ( ( ! [A: $i > $o] :
          ( ( isIndSet @ A )
         => ( A @ ( s @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) ) ) )
      & ! [A: $i] :
          ( ( p @ e @ ( s @ ( s @ e ) ) )
         => ( p @ e @ ( s @ ( s @ e ) ) ) ) )
    = ( isIndSet
      @ ^ [A: $i] : ( p @ e @ ( s @ ( s @ e ) ) ) ) ),
    inference(pre_uni,[status(thm)],[7858:[bind(A,$thf( ^ [B: $i] : ( p @ e @ ( s @ ( s @ e ) ) ) ))]]) ).

thf(7970,plain,
    ( ( ! [A: $i > $o] :
          ( ( isIndSet @ A )
         => ( A @ ( s @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) ) ) ) )
    = ( isIndSet
      @ ^ [A: $i] : ( p @ e @ ( s @ ( s @ e ) ) ) ) ),
    inference(simp,[status(thm)],[7913]) ).

thf(8543,plain,
    ( ( isIndSet
      @ ^ [A: $i] :
        ! [B: $i > $o] :
          ( ( isIndSet @ B )
         => ( B @ ( s @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) ) ) ) )
    = ( ! [A: $i > $o] :
          ( ( isIndSet @ A )
         => ( A @ ( s @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) ) ) ) ) ),
    inference(rewrite,[status(thm)],[7970,7285]) ).

thf(31,plain,
    ! [A: $i] :
      ( ~ ( d @ ( s @ e ) )
      | ( ( f @ A @ e )
       != ( f @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) ) ) ),
    inference(paramod_ordered,[status(thm)],[13,10]) ).

thf(33,plain,
    ! [A: $i] :
      ( ~ ( d @ ( s @ e ) )
      | ( A
       != ( s @ ( s @ ( s @ ( s @ e ) ) ) ) )
      | ( ( s @ ( s @ ( s @ ( s @ e ) ) ) )
       != e ) ),
    inference(simp,[status(thm)],[31]) ).

thf(34,plain,
    ( ~ ( d @ ( s @ e ) )
    | ( ( s @ ( s @ ( s @ ( s @ e ) ) ) )
     != e ) ),
    inference(simp,[status(thm)],[33]) ).

thf(35,plain,
    ( ( ( s @ ( s @ ( s @ ( s @ e ) ) ) )
     != e )
    | ( ( d @ ( s @ e ) )
     != ( d @ e ) ) ),
    inference(paramod_ordered,[status(thm)],[20,34]) ).

thf(36,plain,
    ( ( ( s @ ( s @ ( s @ ( s @ e ) ) ) )
     != e )
    | ( ( s @ e )
     != e ) ),
    inference(simp,[status(thm)],[35]) ).

thf(37,plain,
    ( ( ( s @ e )
     != e )
    | ( ( s @ ( s @ ( s @ ( s @ e ) ) ) )
     != ( s @ e ) )
    | ( e != e ) ),
    inference(eqfactor_ordered,[status(thm)],[36]) ).

thf(39,plain,
    ( ( ( s @ e )
     != e )
    | ( ( s @ ( s @ ( s @ e ) ) )
     != e ) ),
    inference(simp,[status(thm)],[37]) ).

thf(40,plain,
    ( ( ( s @ e )
     != e )
    | ( ( s @ ( s @ ( s @ e ) ) )
     != ( s @ e ) )
    | ( e != e ) ),
    inference(eqfactor_ordered,[status(thm)],[39]) ).

thf(42,plain,
    ( ( ( s @ e )
     != e )
    | ( ( s @ ( s @ e ) )
     != e ) ),
    inference(simp,[status(thm)],[40]) ).

thf(75,plain,
    ( ( ( s @ e )
     != e )
    | ( ( s @ ( s @ e ) )
     != ( s @ e ) )
    | ( e != e ) ),
    inference(eqfactor_ordered,[status(thm)],[42]) ).

thf(77,plain,
    ( ( ( s @ e )
     != e )
    | ( ( s @ e )
     != e ) ),
    inference(simp,[status(thm)],[75]) ).

thf(78,plain,
    ( s @ e )
 != e,
    inference(simp,[status(thm)],[77]) ).

thf(14031,plain,
    ( ( isIndSet
      @ ^ [A: $i] :
          ( isIndSet
          @ ^ [B: $i] :
            ! [C: $i] :
              ( ( d @ ( s @ C ) )
             => ( d @ ( s @ ( s @ C ) ) ) ) ) )
    = ( isIndSet
      @ ^ [A: $i] : ( d @ ( s @ A ) ) ) ),
    inference(rewrite,[status(thm)],[3363,3053]) ).

thf(14423,plain,
    ( ( isIndSet
      @ ^ [A: $i] :
        ! [B: $i] :
          ( ( d @ ( s @ B ) )
         => ( d @ ( s @ ( s @ B ) ) ) ) )
    = ( isIndSet
      @ ^ [A: $i] : ( d @ ( s @ A ) ) ) ),
    inference(rewrite,[status(thm)],[14031,3053]) ).

thf(5,axiom,
    ! [A: $i,B: $i] :
      ( ( f @ ( s @ A ) @ ( s @ B ) )
      = ( f @ A @ ( f @ ( s @ A ) @ B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',a3) ).

thf(17,plain,
    ! [A: $i,B: $i] :
      ( ( f @ ( s @ A ) @ ( s @ B ) )
      = ( f @ A @ ( f @ ( s @ A ) @ B ) ) ),
    inference(defexp_and_simp_and_etaexpand,[status(thm)],[5]) ).

thf(18,plain,
    ! [B: $i,A: $i] :
      ( ( f @ ( s @ A ) @ ( s @ B ) )
      = ( f @ A @ ( f @ ( s @ A ) @ B ) ) ),
    inference(cnf,[status(esa)],[17]) ).

thf(19,plain,
    ! [B: $i,A: $i] :
      ( ( f @ ( s @ A ) @ ( s @ B ) )
      = ( f @ A @ ( f @ ( s @ A ) @ B ) ) ),
    inference(lifteq,[status(thm)],[18]) ).

thf(103,plain,
    ! [C: $i,B: $i,A: $i] :
      ( ( ( s @ ( s @ ( f @ e @ A ) ) )
        = ( f @ B @ ( f @ ( s @ B ) @ C ) ) )
      | ( ( f @ e @ ( s @ A ) )
       != ( f @ ( s @ B ) @ ( s @ C ) ) ) ),
    inference(paramod_ordered,[status(thm)],[16,19]) ).

thf(106,plain,
    ! [C: $i,B: $i,A: $i] :
      ( ( ( s @ ( s @ ( f @ e @ A ) ) )
        = ( f @ B @ ( f @ ( s @ B ) @ C ) ) )
      | ( ( s @ B )
       != e )
      | ( ( s @ A )
       != ( s @ C ) ) ),
    inference(simp,[status(thm)],[103]) ).

thf(4511,plain,
    ! [A: $i] :
      ( ~ ( d @ A )
      | ( d
       != ( ^ [B: $i] : $false ) )
      | ( ( d @ ( s @ A ) )
       != ( d @ ( s @ sk2 ) ) ) ),
    inference(paramod_ordered,[status(thm)],[22,4091]) ).

thf(4512,plain,
    ( ~ ( d @ sk2 )
    | ( d
     != ( ^ [A: $i] : $false ) ) ),
    inference(pattern_uni,[status(thm)],[4511:[bind(A,$thf( sk2 ))]]) ).

thf(6039,plain,
    ! [A: $i > $o] :
      ( ~ ( isIndSet @ A )
      | ( d
       != ( ^ [B: $i] : $false ) )
      | ( ( A @ e )
       != ( d @ sk2 ) ) ),
    inference(paramod_ordered,[status(thm)],[67,4512]) ).

thf(6054,plain,
    ( ~ ( isIndSet
        @ ^ [A: $i] : ( d @ sk2 ) )
    | ( d
     != ( ^ [A: $i] : $false ) ) ),
    inference(pre_uni,[status(thm)],[6039:[bind(A,$thf( ^ [B: $i] : ( d @ sk2 ) ))]]) ).

thf(768,plain,
    ( ~ ! [A: $i] :
          ( ( d @ ( s @ A ) )
         => ( d @ ( s @ ( s @ A ) ) ) )
    | ( isIndSet
      @ ^ [A: $i] : ( d @ ( s @ A ) ) ) ),
    inference(bool_ext,[status(thm)],[268]) ).

thf(806,plain,
    ( ( isIndSet
      @ ^ [A: $i] : ( d @ ( s @ A ) ) )
    | ( d @ ( s @ sk6 ) ) ),
    inference(cnf,[status(esa)],[768]) ).

thf(11917,plain,
    ! [C: $i,B: $i,A: $i] :
      ( ( ( ! [D: $i > $o] :
              ( ( isIndSet @ D )
             => ( D @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( f @ e @ A ) ) ) ) ) ) ) ) ) )
        = ( ! [D: $i > $o] :
              ( ( isIndSet @ D )
             => ( D @ ( f @ B @ C ) ) ) ) )
      | ( ( p @ e @ ( s @ ( s @ ( s @ A ) ) ) )
       != ( p @ B @ C ) ) ),
    inference(paramod_ordered,[status(thm)],[7433,29]) ).

thf(11918,plain,
    ! [A: $i] :
      ( ( ! [B: $i > $o] :
            ( ( isIndSet @ B )
           => ( B @ ( f @ e @ ( s @ ( s @ ( s @ A ) ) ) ) ) ) )
      = ( ! [B: $i > $o] :
            ( ( isIndSet @ B )
           => ( B @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( f @ e @ A ) ) ) ) ) ) ) ) ) ) ),
    inference(pattern_uni,[status(thm)],[11917:[bind(A,$thf( F )),bind(B,$thf( e )),bind(C,$thf( s @ ( s @ ( s @ F ) ) ))]]) ).

thf(12171,plain,
    ! [A: $i] :
      ( ( ! [B: $i > $o] :
            ( ( isIndSet @ B )
           => ( B @ ( f @ e @ ( s @ ( s @ ( s @ A ) ) ) ) ) ) )
      = ( ! [B: $i > $o] :
            ( ( isIndSet @ B )
           => ( B @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( f @ e @ A ) ) ) ) ) ) ) ) ) ) ),
    inference(simp,[status(thm)],[11918]) ).

thf(13719,plain,
    ! [A: $i] :
      ( ( ! [B: $i > $o] :
            ( ( isIndSet @ B )
           => ( B @ ( s @ ( s @ ( f @ e @ ( s @ ( s @ A ) ) ) ) ) ) ) )
      = ( ! [B: $i > $o] :
            ( ( isIndSet @ B )
           => ( B @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( f @ e @ A ) ) ) ) ) ) ) ) ) ) ),
    inference(rewrite,[status(thm)],[12171,16]) ).

thf(818,plain,
    ! [A: $i] :
      ( ( d @ ( s @ A ) )
      | ( ( d @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) ) ) ) ) )
       != ( d @ A ) ) ),
    inference(paramod_ordered,[status(thm)],[479,22]) ).

thf(819,plain,
    d @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) ) ) ) ) ),
    inference(pattern_uni,[status(thm)],[818:[bind(A,$thf( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) ) ) ) ))]]) ).

thf(2957,plain,
    ! [A: $i] :
      ( ( d @ ( s @ A ) )
      | ( ( d @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) ) ) ) ) ) )
       != ( d @ A ) ) ),
    inference(paramod_ordered,[status(thm)],[819,22]) ).

thf(2958,plain,
    d @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) ) ) ) ) ) ),
    inference(pattern_uni,[status(thm)],[2957:[bind(A,$thf( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) ) ) ) ) ))]]) ).

thf(3208,plain,
    ! [A: $i] :
      ( ( d @ ( s @ A ) )
      | ( ( d @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) ) ) ) ) ) ) )
       != ( d @ A ) ) ),
    inference(paramod_ordered,[status(thm)],[2958,22]) ).

thf(3209,plain,
    d @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) ) ) ) ) ) ) ),
    inference(pattern_uni,[status(thm)],[3208:[bind(A,$thf( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) ) ) ) ) ) ))]]) ).

thf(5353,plain,
    ! [A: $i] :
      ( ( d @ ( s @ A ) )
      | ( ( d @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) ) ) ) ) ) ) ) )
       != ( d @ A ) ) ),
    inference(paramod_ordered,[status(thm)],[3209,22]) ).

thf(5354,plain,
    d @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) ) ) ) ) ) ) ) ),
    inference(pattern_uni,[status(thm)],[5353:[bind(A,$thf( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) ) ) ) ) ) ) ))]]) ).

thf(10537,plain,
    ! [A: $i] :
      ( ( d @ ( s @ A ) )
      | ( ( d @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) ) ) ) ) ) ) ) ) )
       != ( d @ A ) ) ),
    inference(paramod_ordered,[status(thm)],[5354,22]) ).

thf(10538,plain,
    d @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) ) ) ) ) ) ) ) ) ),
    inference(pattern_uni,[status(thm)],[10537:[bind(A,$thf( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) ) ) ) ) ) ) ) ))]]) ).

thf(19976,plain,
    ! [B: $i,A: $i] :
      ( ( ( ! [C: $i > $o] :
              ( ( isIndSet @ C )
             => ( C @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( f @ e @ A ) ) ) ) ) ) ) ) ) ) ) )
        = ( ! [C: $i > $o] :
              ( ( isIndSet @ C )
             => ( C @ ( s @ ( s @ ( s @ ( s @ ( f @ e @ B ) ) ) ) ) ) ) ) )
      | ( ( p @ e @ ( s @ ( s @ ( s @ ( s @ A ) ) ) ) )
       != ( p @ e @ ( s @ ( s @ B ) ) ) ) ),
    inference(paramod_ordered,[status(thm)],[12179,3570]) ).

thf(19977,plain,
    ! [A: $i] :
      ( ( ! [B: $i > $o] :
            ( ( isIndSet @ B )
           => ( B @ ( s @ ( s @ ( s @ ( s @ ( f @ e @ ( s @ ( s @ A ) ) ) ) ) ) ) ) ) )
      = ( ! [B: $i > $o] :
            ( ( isIndSet @ B )
           => ( B @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( f @ e @ A ) ) ) ) ) ) ) ) ) ) ) ) ),
    inference(pattern_uni,[status(thm)],[19976:[bind(A,$thf( D )),bind(B,$thf( s @ ( s @ D ) ))]]) ).

thf(20108,plain,
    ! [A: $i] :
      ( ( ! [B: $i > $o] :
            ( ( isIndSet @ B )
           => ( B @ ( s @ ( s @ ( s @ ( s @ ( f @ e @ ( s @ ( s @ A ) ) ) ) ) ) ) ) ) )
      = ( ! [B: $i > $o] :
            ( ( isIndSet @ B )
           => ( B @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( f @ e @ A ) ) ) ) ) ) ) ) ) ) ) ) ),
    inference(simp,[status(thm)],[19977]) ).

thf(23814,plain,
    ! [A: $i] :
      ( ( ! [B: $i > $o] :
            ( ( isIndSet @ B )
           => ( B @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( f @ e @ ( s @ A ) ) ) ) ) ) ) ) ) ) )
      = ( ! [B: $i > $o] :
            ( ( isIndSet @ B )
           => ( B @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( f @ e @ A ) ) ) ) ) ) ) ) ) ) ) ) ),
    inference(rewrite,[status(thm)],[20108,13552]) ).

thf(3940,plain,
    ! [A: $i > $o] :
      ( ~ ( isIndSet @ A )
      | ( d
       != ( ^ [B: $i] : $false ) )
      | ( ( A @ e )
       != ( isIndSet
          @ ^ [B: $i] : ( d @ sk69 ) ) ) ),
    inference(paramod_ordered,[status(thm)],[67,3471]) ).

thf(3955,plain,
    ( ~ ( isIndSet
        @ ^ [A: $i] :
            ( isIndSet
            @ ^ [B: $i] : ( d @ sk69 ) ) )
    | ( d
     != ( ^ [A: $i] : $false ) ) ),
    inference(pre_uni,[status(thm)],[3940:[bind(A,$thf( ^ [B: $i] : ( isIndSet @ ^ [C: $i] : ( d @ sk69 ) ) ))]]) ).

thf(6102,plain,
    ! [A: $i] :
      ( ( isIndSet @ d )
      | ( d @ ( s @ A ) )
      | ( ( d @ ( sk1 @ d ) )
       != ( d @ A ) ) ),
    inference(paramod_ordered,[status(thm)],[1391,22]) ).

thf(6103,plain,
    ( ( isIndSet @ d )
    | ( d @ ( s @ ( sk1 @ d ) ) ) ),
    inference(pattern_uni,[status(thm)],[6102:[bind(A,$thf( sk1 @ d ))]]) ).

thf(8227,plain,
    ( ( d
     != ( ^ [A: $i] : $false ) )
    | ( ( isIndSet
        @ ^ [A: $i] : ( d @ sk2 ) )
     != ( isIndSet
        @ ^ [A: $i] : $true ) ) ),
    inference(paramod_ordered,[status(thm)],[70,6054]) ).

thf(8289,plain,
    ( ( d
     != ( ^ [A: $i] : $false ) )
    | ( ( ^ [A: $i] : ( d @ sk2 ) )
     != ( ^ [A: $i] : $true ) ) ),
    inference(simp,[status(thm)],[8227]) ).

thf(6033,plain,
    ( ( d
     != ( ^ [A: $i] : $false ) )
    | ( ( d @ ( s @ ( s @ e ) ) )
     != ( d @ sk2 ) ) ),
    inference(paramod_ordered,[status(thm)],[264,4512]) ).

thf(6047,plain,
    ( ( d
     != ( ^ [A: $i] : $false ) )
    | ( ( s @ ( s @ e ) )
     != sk2 ) ),
    inference(simp,[status(thm)],[6033]) ).

thf(12260,plain,
    ( ( d
     != ( ^ [A: $i] : $false ) )
    | ( ( isIndSet
        @ ^ [A: $i] :
            ( isIndSet
            @ ^ [B: $i] : ( d @ sk69 ) ) )
     != ( isIndSet
        @ ^ [A: $i] : $true ) ) ),
    inference(paramod_ordered,[status(thm)],[70,3955]) ).

thf(12350,plain,
    ( ( d
     != ( ^ [A: $i] : $false ) )
    | ( ( ^ [A: $i] :
            ( isIndSet
            @ ^ [B: $i] : ( d @ sk69 ) ) )
     != ( ^ [A: $i] : $true ) ) ),
    inference(simp,[status(thm)],[12260]) ).

thf(13070,plain,
    ( ( ( ^ [A: $i] : ( isIndSet @ d ) )
     != ( ^ [A: $i] : $false ) )
    | ( ( d @ ( s @ e ) )
     != ( d @ sk2 ) ) ),
    inference(paramod_ordered,[status(thm)],[250,12927]) ).

thf(13104,plain,
    ( ( ( ^ [A: $i] : ( isIndSet @ d ) )
     != ( ^ [A: $i] : $false ) )
    | ( ( s @ e )
     != sk2 ) ),
    inference(simp,[status(thm)],[13070]) ).

thf(259,plain,
    ( ~ $true
    | ( ( s @ ( s @ ( s @ ( s @ e ) ) ) )
     != e ) ),
    inference(rewrite,[status(thm)],[34,250]) ).

thf(260,plain,
    ( s @ ( s @ ( s @ ( s @ e ) ) ) )
 != e,
    inference(simp,[status(thm)],[259]) ).

thf(28,plain,
    ! [A: $i] :
      ( ( p @ A )
      = ( ^ [B: $i] :
          ! [C: $i > $o] :
            ( ( isIndSet @ C )
           => ( C @ ( f @ A @ B ) ) ) ) ),
    inference(func_ext,[status(esa)],[26]) ).

thf(8249,plain,
    ! [A: $i > $o] :
      ( ~ ( isIndSet @ A )
      | ( d
       != ( ^ [B: $i] : $false ) )
      | ( ( A @ e )
       != ( isIndSet
          @ ^ [B: $i] : ( d @ sk2 ) ) ) ),
    inference(paramod_ordered,[status(thm)],[67,6054]) ).

thf(8290,plain,
    ( ~ ( isIndSet
        @ ^ [A: $i] :
            ( isIndSet
            @ ^ [B: $i] : ( d @ sk2 ) ) )
    | ( d
     != ( ^ [A: $i] : $false ) ) ),
    inference(pre_uni,[status(thm)],[8249:[bind(A,$thf( ^ [B: $i] : ( isIndSet @ ^ [C: $i] : ( d @ sk2 ) ) ))]]) ).

thf(14838,plain,
    ( ( d
     != ( ^ [A: $i] : $false ) )
    | ( ( isIndSet
        @ ^ [A: $i] :
            ( isIndSet
            @ ^ [B: $i] : ( d @ sk2 ) ) )
     != ( isIndSet
        @ ^ [A: $i] : $true ) ) ),
    inference(paramod_ordered,[status(thm)],[70,8290]) ).

thf(14958,plain,
    ( ( d
     != ( ^ [A: $i] : $false ) )
    | ( ( ^ [A: $i] :
            ( isIndSet
            @ ^ [B: $i] : ( d @ sk2 ) ) )
     != ( ^ [A: $i] : $true ) ) ),
    inference(simp,[status(thm)],[14838]) ).

thf(2515,plain,
    ( ~ ( isIndSet
        @ ^ [A: $i] : ( d @ ( s @ A ) ) )
    | ( ( isIndSet
        @ ^ [A: $i] :
            ( isIndSet
            @ ^ [B: $i] : ( d @ ( s @ B ) ) ) )
     != ( isIndSet
        @ ^ [A: $i] : $false ) ) ),
    inference(paramod_ordered,[status(thm)],[2219,2403]) ).

thf(2560,plain,
    ( ~ ( isIndSet
        @ ^ [A: $i] : ( d @ ( s @ A ) ) )
    | ( ( ^ [A: $i] :
            ( isIndSet
            @ ^ [B: $i] : ( d @ ( s @ B ) ) ) )
     != ( ^ [A: $i] : $false ) ) ),
    inference(simp,[status(thm)],[2515]) ).

thf(65,plain,
    ! [A: $i > $o] :
      ( ( isIndSet @ A )
      | ~ ( A @ e )
      | ~ ( A @ ( s @ ( sk1 @ A ) ) ) ),
    inference(cnf,[status(esa)],[56]) ).

thf(98,plain,
    ~ ( d @ ( f @ ( s @ ( s @ ( s @ e ) ) ) @ ( f @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) @ ( s @ ( s @ ( s @ e ) ) ) ) ) ),
    inference(rewrite,[status(thm)],[10,19]) ).

thf(162,plain,
    ~ ( d @ ( f @ ( s @ ( s @ ( s @ e ) ) ) @ ( f @ ( s @ ( s @ ( s @ e ) ) ) @ ( f @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) @ ( s @ ( s @ e ) ) ) ) ) ),
    inference(rewrite,[status(thm)],[98,19]) ).

thf(165,plain,
    ! [A: $i] :
      ( ~ ( d @ ( f @ ( s @ ( s @ ( s @ e ) ) ) @ ( s @ e ) ) )
      | ( ( f @ A @ e )
       != ( f @ ( s @ ( s @ ( s @ e ) ) ) @ ( f @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) @ ( s @ ( s @ e ) ) ) ) ) ),
    inference(paramod_ordered,[status(thm)],[13,162]) ).

thf(175,plain,
    ! [A: $i] :
      ( ~ ( d @ ( f @ ( s @ ( s @ ( s @ e ) ) ) @ ( s @ e ) ) )
      | ( A
       != ( s @ ( s @ ( s @ e ) ) ) )
      | ( ( f @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) @ ( s @ ( s @ e ) ) )
       != e ) ),
    inference(simp,[status(thm)],[165]) ).

thf(185,plain,
    ( ~ ( d @ ( f @ ( s @ ( s @ ( s @ e ) ) ) @ ( s @ e ) ) )
    | ( ( f @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) @ ( s @ ( s @ e ) ) )
     != e ) ),
    inference(simp,[status(thm)],[175]) ).

thf(28019,plain,
    ( ~ ( d @ ( f @ ( s @ ( s @ e ) ) @ ( f @ ( s @ ( s @ ( s @ e ) ) ) @ e ) ) )
    | ( ( f @ ( s @ ( s @ ( s @ e ) ) ) @ ( f @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) @ ( s @ e ) ) )
     != e ) ),
    inference(rewrite,[status(thm)],[185,19]) ).

thf(25460,plain,
    ! [A: $i] :
      ( ~ ( d @ A )
      | ( ( ^ [B: $i] : ( d @ ( s @ B ) ) )
       != ( ^ [B: $i] : $false ) )
      | ( ( d @ ( s @ A ) )
       != ( d @ ( s @ sk91 ) ) ) ),
    inference(paramod_ordered,[status(thm)],[22,25384]) ).

thf(25461,plain,
    ( ~ ( d @ sk91 )
    | ( ( ^ [A: $i] : ( d @ ( s @ A ) ) )
     != ( ^ [A: $i] : $false ) ) ),
    inference(pattern_uni,[status(thm)],[25460:[bind(A,$thf( sk91 ))]]) ).

thf(25518,plain,
    ! [A: $i > $o] :
      ( ~ ( isIndSet @ A )
      | ( ( ^ [B: $i] : ( d @ ( s @ B ) ) )
       != ( ^ [B: $i] : $false ) )
      | ( ( A @ e )
       != ( d @ sk91 ) ) ),
    inference(paramod_ordered,[status(thm)],[67,25461]) ).

thf(25534,plain,
    ( ~ ( isIndSet
        @ ^ [A: $i] : ( d @ sk91 ) )
    | ( ( ^ [A: $i] : ( d @ ( s @ A ) ) )
     != ( ^ [A: $i] : $false ) ) ),
    inference(pre_uni,[status(thm)],[25518:[bind(A,$thf( ^ [B: $i] : ( d @ sk91 ) ))]]) ).

thf(3461,plain,
    ( ( d
     != ( ^ [A: $i] : $false ) )
    | ( ( d @ ( s @ ( s @ e ) ) )
     != ( d @ sk69 ) ) ),
    inference(paramod_ordered,[status(thm)],[264,2989]) ).

thf(3482,plain,
    ( ( d
     != ( ^ [A: $i] : $false ) )
    | ( ( s @ ( s @ e ) )
     != sk69 ) ),
    inference(simp,[status(thm)],[3461]) ).

thf(11617,plain,
    ( ( ( isIndSet
        @ ^ [A: $i] :
            ( isIndSet
            @ ^ [B: $i] :
              ! [C: $i] :
                ( ( d @ ( s @ ( s @ C ) ) )
               => ( d @ ( s @ ( s @ ( s @ C ) ) ) ) ) ) )
      = ( isIndSet
        @ ^ [A: $i] : ( d @ ( s @ ( s @ A ) ) ) ) )
    | ( ( isIndSet
        @ ^ [A: $i] : ( d @ ( s @ ( s @ A ) ) ) )
     != ( isIndSet
        @ ^ [A: $i] : ( d @ ( s @ ( s @ A ) ) ) ) ) ),
    inference(paramod_ordered,[status(thm)],[10314,9631]) ).

thf(11618,plain,
    ( ( isIndSet
      @ ^ [A: $i] :
          ( isIndSet
          @ ^ [B: $i] :
            ! [C: $i] :
              ( ( d @ ( s @ ( s @ C ) ) )
             => ( d @ ( s @ ( s @ ( s @ C ) ) ) ) ) ) )
    = ( isIndSet
      @ ^ [A: $i] : ( d @ ( s @ ( s @ A ) ) ) ) ),
    inference(pattern_uni,[status(thm)],[11617:[]]) ).

thf(19292,plain,
    ( ( ( isIndSet
        @ ^ [A: $i] :
            ( isIndSet
            @ ^ [B: $i] :
                ( isIndSet
                @ ^ [C: $i] :
                  ! [D: $i] :
                    ( ( d @ ( s @ ( s @ D ) ) )
                   => ( d @ ( s @ ( s @ ( s @ D ) ) ) ) ) ) ) )
      = ( isIndSet
        @ ^ [A: $i] : ( d @ ( s @ ( s @ A ) ) ) ) )
    | ( ( isIndSet
        @ ^ [A: $i] : ( d @ ( s @ ( s @ A ) ) ) )
     != ( isIndSet
        @ ^ [A: $i] : ( d @ ( s @ ( s @ A ) ) ) ) ) ),
    inference(paramod_ordered,[status(thm)],[11618,9631]) ).

thf(19293,plain,
    ( ( isIndSet
      @ ^ [A: $i] :
          ( isIndSet
          @ ^ [B: $i] :
              ( isIndSet
              @ ^ [C: $i] :
                ! [D: $i] :
                  ( ( d @ ( s @ ( s @ D ) ) )
                 => ( d @ ( s @ ( s @ ( s @ D ) ) ) ) ) ) ) )
    = ( isIndSet
      @ ^ [A: $i] : ( d @ ( s @ ( s @ A ) ) ) ) ),
    inference(pattern_uni,[status(thm)],[19292:[]]) ).

thf(30333,plain,
    ( ( ( isIndSet
        @ ^ [A: $i] :
            ( isIndSet
            @ ^ [B: $i] :
                ( isIndSet
                @ ^ [C: $i] :
                    ( isIndSet
                    @ ^ [D: $i] : ( d @ ( s @ ( s @ D ) ) ) ) ) ) )
      = ( isIndSet
        @ ^ [A: $i] : ( d @ ( s @ ( s @ A ) ) ) ) )
    | ( ( ! [A: $i] :
            ( ( d @ ( s @ ( s @ A ) ) )
           => ( d @ ( s @ ( s @ ( s @ A ) ) ) ) ) )
     != ( ! [A: $i] :
            ( ( d @ ( s @ ( s @ A ) ) )
           => ( d @ ( s @ ( s @ ( s @ A ) ) ) ) ) ) ) ),
    inference(paramod_ordered,[status(thm)],[9686,19293]) ).

thf(30334,plain,
    ( ( isIndSet
      @ ^ [A: $i] :
          ( isIndSet
          @ ^ [B: $i] :
              ( isIndSet
              @ ^ [C: $i] :
                  ( isIndSet
                  @ ^ [D: $i] : ( d @ ( s @ ( s @ D ) ) ) ) ) ) )
    = ( isIndSet
      @ ^ [A: $i] : ( d @ ( s @ ( s @ A ) ) ) ) ),
    inference(pattern_uni,[status(thm)],[30333:[]]) ).

thf(30832,plain,
    ( ( isIndSet
      @ ^ [A: $i] :
          ( isIndSet
          @ ^ [B: $i] :
              ( isIndSet
              @ ^ [C: $i] : ( d @ ( s @ ( s @ C ) ) ) ) ) )
    = ( isIndSet
      @ ^ [A: $i] : ( d @ ( s @ ( s @ A ) ) ) ) ),
    inference(rewrite,[status(thm)],[30334,9631]) ).

thf(1074,plain,
    ( ( isIndSet @ d )
    | ~ ! [A: $i] :
          ( ( d @ A )
         => ( d @ ( s @ A ) ) ) ),
    inference(bool_ext,[status(thm)],[1044]) ).

thf(1111,plain,
    ( ( d @ sk8 )
    | ( isIndSet @ d ) ),
    inference(cnf,[status(esa)],[1074]) ).

thf(8949,plain,
    ( ( ( ^ [A: $i] : ( isIndSet @ d ) )
     != ( ^ [A: $i] : $false ) )
    | ( ( d @ ( s @ e ) )
     != ( d @ sk68 ) ) ),
    inference(paramod_ordered,[status(thm)],[250,8837]) ).

thf(8984,plain,
    ( ( ( ^ [A: $i] : ( isIndSet @ d ) )
     != ( ^ [A: $i] : $false ) )
    | ( ( s @ e )
     != sk68 ) ),
    inference(simp,[status(thm)],[8949]) ).

thf(2992,plain,
    ( ( d
     != ( ^ [A: $i] : $false ) )
    | ( ( d @ ( s @ sk69 ) )
     != ( d @ ( s @ e ) ) ) ),
    inference(paramod_ordered,[status(thm)],[250,2481]) ).

thf(3001,plain,
    ( ( d
     != ( ^ [A: $i] : $false ) )
    | ( ( s @ sk69 )
     != ( s @ e ) ) ),
    inference(simp,[status(thm)],[2992]) ).

thf(12908,plain,
    ( ( ( ^ [A: $i] : ( isIndSet @ d ) )
     != ( ^ [A: $i] : $false ) )
    | ( ( d @ ( s @ sk2 ) )
     != ( d @ e ) ) ),
    inference(paramod_ordered,[status(thm)],[20,4018]) ).

thf(12974,plain,
    ( ( ( ^ [A: $i] : ( isIndSet @ d ) )
     != ( ^ [A: $i] : $false ) )
    | ( ( s @ sk2 )
     != e ) ),
    inference(simp,[status(thm)],[12908]) ).

thf(164,plain,
    ! [A: $i] :
      ( ~ ( d @ ( s @ e ) )
      | ( ( f @ A @ e )
       != ( f @ ( s @ ( s @ ( s @ e ) ) ) @ ( f @ ( s @ ( s @ ( s @ e ) ) ) @ ( f @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) @ ( s @ ( s @ e ) ) ) ) ) ) ),
    inference(paramod_ordered,[status(thm)],[13,162]) ).

thf(174,plain,
    ! [A: $i] :
      ( ~ ( d @ ( s @ e ) )
      | ( A
       != ( s @ ( s @ ( s @ e ) ) ) )
      | ( ( f @ ( s @ ( s @ ( s @ e ) ) ) @ ( f @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) @ ( s @ ( s @ e ) ) ) )
       != e ) ),
    inference(simp,[status(thm)],[164]) ).

thf(184,plain,
    ( ~ ( d @ ( s @ e ) )
    | ( ( f @ ( s @ ( s @ ( s @ e ) ) ) @ ( f @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) @ ( s @ ( s @ e ) ) ) )
     != e ) ),
    inference(simp,[status(thm)],[174]) ).

thf(27015,plain,
    ( ~ $true
    | ( ( f @ ( s @ ( s @ ( s @ e ) ) ) @ ( f @ ( s @ ( s @ ( s @ e ) ) ) @ ( f @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) @ ( s @ e ) ) ) )
     != e ) ),
    inference(rewrite,[status(thm)],[184,19,250]) ).

thf(27016,plain,
    ( f @ ( s @ ( s @ ( s @ e ) ) ) @ ( f @ ( s @ ( s @ ( s @ e ) ) ) @ ( f @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) @ ( s @ e ) ) ) )
 != e,
    inference(simp,[status(thm)],[27015]) ).

thf(172,plain,
    ! [B: $i,A: $i] :
      ( ~ ( d @ ( f @ A @ ( f @ ( s @ A ) @ B ) ) )
      | ( ( f @ ( s @ A ) @ ( s @ B ) )
       != ( f @ ( s @ ( s @ ( s @ e ) ) ) @ ( f @ ( s @ ( s @ ( s @ e ) ) ) @ ( f @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) @ ( s @ ( s @ e ) ) ) ) ) ) ),
    inference(paramod_ordered,[status(thm)],[19,162]) ).

thf(179,plain,
    ! [B: $i,A: $i] :
      ( ~ ( d @ ( f @ A @ ( f @ ( s @ A ) @ B ) ) )
      | ( ( s @ A )
       != ( s @ ( s @ ( s @ e ) ) ) )
      | ( ( s @ B )
       != ( f @ ( s @ ( s @ ( s @ e ) ) ) @ ( f @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) @ ( s @ ( s @ e ) ) ) ) ) ),
    inference(simp,[status(thm)],[172]) ).

thf(24149,plain,
    ! [B: $i,A: $i] :
      ( ~ ( d @ ( f @ A @ ( f @ ( s @ A ) @ B ) ) )
      | ( ( s @ A )
       != ( s @ ( s @ ( s @ e ) ) ) )
      | ( ( s @ B )
       != ( f @ ( s @ ( s @ ( s @ e ) ) ) @ ( f @ ( s @ ( s @ ( s @ e ) ) ) @ ( f @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) @ ( s @ e ) ) ) ) ) ),
    inference(rewrite,[status(thm)],[179,19]) ).

thf(4516,plain,
    ! [A: $i > $o] :
      ( ~ ( isIndSet @ A )
      | ( d
       != ( ^ [B: $i] : $false ) )
      | ( ( A @ e )
       != ( d @ ( s @ sk2 ) ) ) ),
    inference(paramod_ordered,[status(thm)],[67,4091]) ).

thf(4535,plain,
    ( ~ ( isIndSet
        @ ^ [A: $i] : ( d @ ( s @ sk2 ) ) )
    | ( d
     != ( ^ [A: $i] : $false ) ) ),
    inference(pre_uni,[status(thm)],[4516:[bind(A,$thf( ^ [B: $i] : ( d @ ( s @ sk2 ) ) ))]]) ).

thf(102,plain,
    ! [C: $i,B: $i,A: $i] :
      ( ( ( f @ A @ ( f @ ( s @ A ) @ B ) )
        = ( s @ ( s @ ( f @ e @ C ) ) ) )
      | ( ( f @ ( s @ A ) @ ( s @ B ) )
       != ( f @ e @ ( s @ C ) ) ) ),
    inference(paramod_ordered,[status(thm)],[19,16]) ).

thf(105,plain,
    ! [C: $i,B: $i,A: $i] :
      ( ( ( f @ A @ ( f @ ( s @ A ) @ B ) )
        = ( s @ ( s @ ( f @ e @ C ) ) ) )
      | ( ( s @ A )
       != e )
      | ( ( s @ B )
       != ( s @ C ) ) ),
    inference(simp,[status(thm)],[102]) ).

thf(13034,plain,
    ( ( ( ^ [A: $i] : ( isIndSet @ d ) )
     != ( ^ [A: $i] : $false ) )
    | ( ( d @ sk2 )
     != ( d @ e ) ) ),
    inference(paramod_ordered,[status(thm)],[20,12927]) ).

thf(13103,plain,
    ( ( ( ^ [A: $i] : ( isIndSet @ d ) )
     != ( ^ [A: $i] : $false ) )
    | ( sk2 != e ) ),
    inference(simp,[status(thm)],[13034]) ).

thf(173,plain,
    ! [B: $i,A: $i] :
      ( ~ ( d @ ( f @ ( s @ ( s @ ( s @ e ) ) ) @ ( f @ A @ ( f @ ( s @ A ) @ B ) ) ) )
      | ( ( f @ ( s @ A ) @ ( s @ B ) )
       != ( f @ ( s @ ( s @ ( s @ e ) ) ) @ ( f @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) @ ( s @ ( s @ e ) ) ) ) ) ),
    inference(paramod_ordered,[status(thm)],[19,162]) ).

thf(177,plain,
    ! [B: $i,A: $i] :
      ( ~ ( d @ ( f @ ( s @ ( s @ ( s @ e ) ) ) @ ( f @ A @ ( f @ ( s @ A ) @ B ) ) ) )
      | ( ( s @ A )
       != ( s @ ( s @ ( s @ e ) ) ) )
      | ( ( s @ B )
       != ( f @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) @ ( s @ ( s @ e ) ) ) ) ),
    inference(simp,[status(thm)],[173]) ).

thf(22415,plain,
    ! [B: $i,A: $i] :
      ( ~ ( d @ ( f @ ( s @ ( s @ ( s @ e ) ) ) @ ( f @ A @ ( f @ ( s @ A ) @ B ) ) ) )
      | ( ( s @ A )
       != ( s @ ( s @ ( s @ e ) ) ) )
      | ( ( s @ B )
       != ( f @ ( s @ ( s @ ( s @ e ) ) ) @ ( f @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) @ ( s @ e ) ) ) ) ),
    inference(rewrite,[status(thm)],[177,19]) ).

thf(2985,plain,
    ( ( d
     != ( ^ [A: $i] : $false ) )
    | ( ( d @ ( s @ ( s @ e ) ) )
     != ( d @ ( s @ sk69 ) ) ) ),
    inference(paramod_ordered,[status(thm)],[264,2481]) ).

thf(2995,plain,
    ( ( d
     != ( ^ [A: $i] : $false ) )
    | ( ( s @ ( s @ e ) )
     != ( s @ sk69 ) ) ),
    inference(simp,[status(thm)],[2985]) ).

thf(83,plain,
    ! [A: $i > $o] :
      ( ( ( ! [B: $i] :
              ( ( d @ B )
             => ( d @ ( s @ B ) ) )
          & ! [B: $i] :
              ( ( A @ B )
             => ( A @ ( s @ B ) ) ) )
        = ( isIndSet @ A ) )
      | ( ( isIndSet @ d )
       != ( A @ e ) ) ),
    inference(paramod_ordered,[status(thm)],[61,27]) ).

thf(90,plain,
    ( ( ! [A: $i] :
          ( ( d @ A )
         => ( d @ ( s @ A ) ) )
      & ! [A: $i] :
          ( ( isIndSet @ d )
         => ( isIndSet @ d ) ) )
    = ( isIndSet
      @ ^ [A: $i] : ( isIndSet @ d ) ) ),
    inference(pre_uni,[status(thm)],[83:[bind(A,$thf( ^ [B: $i] : ( isIndSet @ d ) ))]]) ).

thf(95,plain,
    ( ( ! [A: $i] :
          ( ( d @ A )
         => ( d @ ( s @ A ) ) ) )
    = ( isIndSet
      @ ^ [A: $i] : ( isIndSet @ d ) ) ),
    inference(simp,[status(thm)],[90]) ).

thf(122,plain,
    ( ( isIndSet
      @ ^ [A: $i] :
          ( isIndSet
          @ ^ [B: $i] :
            ! [C: $i] :
              ( ( d @ C )
             => ( d @ ( s @ C ) ) ) ) )
    = ( ! [A: $i] :
          ( ( d @ A )
         => ( d @ ( s @ A ) ) ) ) ),
    inference(rewrite,[status(thm)],[95,94]) ).

thf(124,plain,
    ( ( isIndSet
      @ ^ [A: $i] :
          ( isIndSet
          @ ^ [B: $i] :
            ! [C: $i] :
              ( ( d @ C )
             => ( d @ ( s @ C ) ) ) ) )
    | ~ ! [A: $i] :
          ( ( d @ A )
         => ( d @ ( s @ A ) ) ) ),
    inference(bool_ext,[status(thm)],[122]) ).

thf(143,plain,
    ( ~ ( d @ ( s @ sk3 ) )
    | ( isIndSet
      @ ^ [A: $i] :
          ( isIndSet
          @ ^ [B: $i] :
            ! [C: $i] :
              ( ( d @ C )
             => ( d @ ( s @ C ) ) ) ) ) ),
    inference(cnf,[status(esa)],[124]) ).

thf(14997,plain,
    ( ~ ( d @ ( s @ sk3 ) )
    | ( isIndSet
      @ ^ [A: $i] :
        ! [B: $i] :
          ( ( d @ B )
         => ( d @ ( s @ B ) ) ) ) ),
    inference(rewrite,[status(thm)],[143,112]) ).

thf(170,plain,
    ! [B: $i,A: $i] :
      ( ~ ( d @ ( f @ ( s @ ( s @ ( s @ e ) ) ) @ ( f @ ( s @ ( s @ ( s @ e ) ) ) @ ( f @ A @ ( f @ ( s @ A ) @ B ) ) ) ) )
      | ( ( f @ ( s @ A ) @ ( s @ B ) )
       != ( f @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) @ ( s @ ( s @ e ) ) ) ) ),
    inference(paramod_ordered,[status(thm)],[19,162]) ).

thf(171,plain,
    ~ ( d @ ( f @ ( s @ ( s @ ( s @ e ) ) ) @ ( f @ ( s @ ( s @ ( s @ e ) ) ) @ ( f @ ( s @ ( s @ ( s @ e ) ) ) @ ( f @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) @ ( s @ e ) ) ) ) ) ),
    inference(pattern_uni,[status(thm)],[170:[bind(A,$thf( s @ ( s @ ( s @ e ) ) )),bind(B,$thf( s @ e ))]]) ).

thf(21023,plain,
    ~ ( d @ ( f @ ( s @ ( s @ ( s @ e ) ) ) @ ( f @ ( s @ ( s @ ( s @ e ) ) ) @ ( f @ ( s @ ( s @ ( s @ e ) ) ) @ ( f @ ( s @ ( s @ ( s @ e ) ) ) @ ( f @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) @ e ) ) ) ) ) ),
    inference(rewrite,[status(thm)],[171,19]) ).

thf(169,plain,
    ( d @ ( f @ ( s @ ( s @ ( s @ e ) ) ) @ ( f @ ( s @ ( s @ ( s @ e ) ) ) @ ( f @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) @ ( s @ ( s @ e ) ) ) ) ) )
 != ( d @ e ),
    inference(paramod_ordered,[status(thm)],[20,162]) ).

thf(176,plain,
    ( f @ ( s @ ( s @ ( s @ e ) ) ) @ ( f @ ( s @ ( s @ ( s @ e ) ) ) @ ( f @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) @ ( s @ ( s @ e ) ) ) ) )
 != e,
    inference(simp,[status(thm)],[169]) ).

thf(21800,plain,
    ( f @ ( s @ ( s @ ( s @ e ) ) ) @ ( f @ ( s @ ( s @ ( s @ e ) ) ) @ ( f @ ( s @ ( s @ ( s @ e ) ) ) @ ( f @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) @ ( s @ e ) ) ) ) )
 != e,
    inference(rewrite,[status(thm)],[176,19]) ).

thf(8945,plain,
    ! [A: $i > $o] :
      ( ~ ( isIndSet @ A )
      | ( ( ^ [B: $i] : ( isIndSet @ d ) )
       != ( ^ [B: $i] : $false ) )
      | ( ( A @ e )
       != ( d @ sk68 ) ) ),
    inference(paramod_ordered,[status(thm)],[67,8837]) ).

thf(8982,plain,
    ( ~ ( isIndSet
        @ ^ [A: $i] : ( d @ sk68 ) )
    | ( ( ^ [A: $i] : ( isIndSet @ d ) )
     != ( ^ [A: $i] : $false ) ) ),
    inference(pre_uni,[status(thm)],[8945:[bind(A,$thf( ^ [B: $i] : ( d @ sk68 ) ))]]) ).

thf(15805,plain,
    ( ( ( ^ [A: $i] : ( isIndSet @ d ) )
     != ( ^ [A: $i] : $false ) )
    | ( ( isIndSet
        @ ^ [A: $i] : ( d @ sk68 ) )
     != ( isIndSet
        @ ^ [A: $i] : $true ) ) ),
    inference(paramod_ordered,[status(thm)],[70,8982]) ).

thf(15923,plain,
    ( ( ( ^ [A: $i] : ( isIndSet @ d ) )
     != ( ^ [A: $i] : $false ) )
    | ( ( ^ [A: $i] : ( d @ sk68 ) )
     != ( ^ [A: $i] : $true ) ) ),
    inference(simp,[status(thm)],[15805]) ).

thf(19842,plain,
    ! [B: $i,A: $i] :
      ( ( ( p @ e @ ( s @ ( s @ ( s @ ( s @ B ) ) ) ) )
        = ( ! [C: $i > $o] :
              ( ( isIndSet @ C )
             => ( C @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) ) ) ) ) ) ) ) ) )
      | ( ( f @ A @ e )
       != ( f @ e @ B ) ) ),
    inference(paramod_ordered,[status(thm)],[13,12179]) ).

thf(19843,plain,
    ( ( p @ e @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) )
    = ( ! [A: $i > $o] :
          ( ( isIndSet @ A )
         => ( A @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) ) ) ) ) ) ) ) ) ),
    inference(pattern_uni,[status(thm)],[19842:[bind(A,$thf( e )),bind(B,$thf( e ))]]) ).

thf(20462,plain,
    ! [A: $i] :
      ( ( ( ! [B: $i > $o] :
              ( ( isIndSet @ B )
             => ( B @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( f @ e @ A ) ) ) ) ) ) ) ) ) )
        = ( ! [B: $i > $o] :
              ( ( isIndSet @ B )
             => ( B @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) ) ) ) ) ) ) ) ) )
      | ( ( p @ e @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) )
       != ( p @ e @ ( s @ ( s @ ( s @ A ) ) ) ) ) ),
    inference(paramod_ordered,[status(thm)],[19843,7433]) ).

thf(20463,plain,
    ( ( ! [A: $i > $o] :
          ( ( isIndSet @ A )
         => ( A @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( f @ e @ ( s @ e ) ) ) ) ) ) ) ) ) ) )
    = ( ! [A: $i > $o] :
          ( ( isIndSet @ A )
         => ( A @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) ) ) ) ) ) ) ) ) ),
    inference(pattern_uni,[status(thm)],[20462:[bind(A,$thf( s @ e ))]]) ).

thf(21400,plain,
    ( ( ! [A: $i > $o] :
          ( ( isIndSet @ A )
         => ( A @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( f @ e @ e ) ) ) ) ) ) ) ) ) ) ) )
    = ( ! [A: $i > $o] :
          ( ( isIndSet @ A )
         => ( A @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) ) ) ) ) ) ) ) ) ),
    inference(rewrite,[status(thm)],[20463,16]) ).

thf(10043,plain,
    ( ( ( ^ [A: $i] : ( isIndSet @ d ) )
     != ( ^ [A: $i] : $false ) )
    | ( ( d @ ( s @ e ) )
     != ( d @ sk71 ) ) ),
    inference(paramod_ordered,[status(thm)],[250,9930]) ).

thf(10068,plain,
    ( ( ( ^ [A: $i] : ( isIndSet @ d ) )
     != ( ^ [A: $i] : $false ) )
    | ( ( s @ e )
     != sk71 ) ),
    inference(simp,[status(thm)],[10043]) ).

thf(4517,plain,
    ( ( d
     != ( ^ [A: $i] : $false ) )
    | ( ( d @ ( s @ sk2 ) )
     != ( d @ ( s @ e ) ) ) ),
    inference(paramod_ordered,[status(thm)],[250,4091]) ).

thf(4526,plain,
    ( ( d
     != ( ^ [A: $i] : $false ) )
    | ( ( s @ sk2 )
     != ( s @ e ) ) ),
    inference(simp,[status(thm)],[4517]) ).

thf(2983,plain,
    ( ( d
     != ( ^ [A: $i] : $false ) )
    | ( ( d @ ( s @ sk69 ) )
     != ( d @ e ) ) ),
    inference(paramod_ordered,[status(thm)],[20,2481]) ).

thf(3002,plain,
    ( ( d
     != ( ^ [A: $i] : $false ) )
    | ( ( s @ sk69 )
     != e ) ),
    inference(simp,[status(thm)],[2983]) ).

thf(45,plain,
    ! [B: $i,A: $i] :
      ( ( ( s @ ( s @ ( f @ e @ B ) ) )
        = ( s @ e ) )
      | ( ( f @ A @ e )
       != ( f @ e @ ( s @ B ) ) ) ),
    inference(paramod_ordered,[status(thm)],[13,16]) ).

thf(48,plain,
    ! [B: $i,A: $i] :
      ( ( ( s @ ( s @ ( f @ e @ B ) ) )
        = ( s @ e ) )
      | ( A != e )
      | ( ( s @ B )
       != e ) ),
    inference(simp,[status(thm)],[45]) ).

thf(49,plain,
    ! [A: $i] :
      ( ( ( s @ ( s @ ( f @ e @ A ) ) )
        = ( s @ e ) )
      | ( ( s @ A )
       != e ) ),
    inference(simp,[status(thm)],[48]) ).

thf(10009,plain,
    ( ( ( ^ [A: $i] : ( isIndSet @ d ) )
     != ( ^ [A: $i] : $false ) )
    | ( ( d @ sk71 )
     != ( d @ e ) ) ),
    inference(paramod_ordered,[status(thm)],[20,9930]) ).

thf(10083,plain,
    ( ( ( ^ [A: $i] : ( isIndSet @ d ) )
     != ( ^ [A: $i] : $false ) )
    | ( sk71 != e ) ),
    inference(simp,[status(thm)],[10009]) ).

thf(7841,plain,
    ! [A: $i] :
      ( ( ( ! [B: $i > $o] :
              ( ( isIndSet @ B )
             => ( B @ ( s @ ( s @ ( f @ e @ A ) ) ) ) ) )
        = ( ! [B: $i > $o] :
              ( ( isIndSet @ B )
             => ( B @ ( s @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) ) ) ) ) )
      | ( ( p @ e @ ( s @ ( s @ e ) ) )
       != ( p @ e @ ( s @ A ) ) ) ),
    inference(paramod_ordered,[status(thm)],[7285,381]) ).

thf(7842,plain,
    ( ( ! [A: $i > $o] :
          ( ( isIndSet @ A )
         => ( A @ ( s @ ( s @ ( f @ e @ ( s @ e ) ) ) ) ) ) )
    = ( ! [A: $i > $o] :
          ( ( isIndSet @ A )
         => ( A @ ( s @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) ) ) ) ) ),
    inference(pattern_uni,[status(thm)],[7841:[bind(A,$thf( s @ e ))]]) ).

thf(7983,plain,
    ( ( ! [A: $i > $o] :
          ( ( isIndSet @ A )
         => ( A @ ( s @ ( s @ ( s @ ( s @ ( f @ e @ e ) ) ) ) ) ) ) )
    = ( ! [A: $i > $o] :
          ( ( isIndSet @ A )
         => ( A @ ( s @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) ) ) ) ) ),
    inference(rewrite,[status(thm)],[7842,16]) ).

thf(361,plain,
    ! [C: $i,B: $i,A: $i] :
      ( ( ( p @ B @ C )
        = ( ! [D: $i > $o] :
              ( ( isIndSet @ D )
             => ( D @ ( s @ e ) ) ) ) )
      | ( ( f @ A @ e )
       != ( f @ B @ C ) ) ),
    inference(paramod_ordered,[status(thm)],[13,29]) ).

thf(362,plain,
    ! [A: $i] :
      ( ( p @ A @ e )
      = ( ! [B: $i > $o] :
            ( ( isIndSet @ B )
           => ( B @ ( s @ e ) ) ) ) ),
    inference(pattern_uni,[status(thm)],[361:[bind(A,$thf( A )),bind(B,$thf( A )),bind(C,$thf( e ))]]) ).

thf(18569,plain,
    ! [A: $i] :
      ( ( d @ ( s @ A ) )
      | ( ( d @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) ) ) ) ) ) ) ) ) ) )
       != ( d @ A ) ) ),
    inference(paramod_ordered,[status(thm)],[10538,22]) ).

thf(18570,plain,
    d @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) ) ) ) ) ) ) ) ) ) ),
    inference(pattern_uni,[status(thm)],[18569:[bind(A,$thf( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) ) ) ) ) ) ) ) ) ))]]) ).

thf(27870,plain,
    ( ( ( ^ [A: $i] : ( d @ ( s @ A ) ) )
     != ( ^ [A: $i] : $false ) )
    | ( ( isIndSet
        @ ^ [A: $i] : ( d @ sk91 ) )
     != ( isIndSet
        @ ^ [A: $i] : $true ) ) ),
    inference(paramod_ordered,[status(thm)],[70,25534]) ).

thf(27925,plain,
    ( ( ( ^ [A: $i] : ( d @ ( s @ A ) ) )
     != ( ^ [A: $i] : $false ) )
    | ( ( ^ [A: $i] : ( d @ sk91 ) )
     != ( ^ [A: $i] : $true ) ) ),
    inference(simp,[status(thm)],[27870]) ).

thf(2602,plain,
    ( ( ( ^ [A: $i] : ( isIndSet @ d ) )
     != ( ^ [A: $i] : $false ) )
    | ( ( isIndSet @ d )
     != ( isIndSet
        @ ^ [A: $i] : $true ) ) ),
    inference(paramod_ordered,[status(thm)],[70,2464]) ).

thf(2625,plain,
    ( ( ( ^ [A: $i] : ( isIndSet @ d ) )
     != ( ^ [A: $i] : $false ) )
    | ( d
     != ( ^ [A: $i] : $true ) ) ),
    inference(simp,[status(thm)],[2602]) ).

thf(25519,plain,
    ( ( ( ^ [A: $i] : ( d @ ( s @ A ) ) )
     != ( ^ [A: $i] : $false ) )
    | ( ( d @ ( s @ e ) )
     != ( d @ sk91 ) ) ),
    inference(paramod_ordered,[status(thm)],[250,25461]) ).

thf(25529,plain,
    ( ( ( ^ [A: $i] : ( d @ ( s @ A ) ) )
     != ( ^ [A: $i] : $false ) )
    | ( ( s @ e )
     != sk91 ) ),
    inference(simp,[status(thm)],[25519]) ).

thf(66,plain,
    ! [B: $i,A: $i > $o] :
      ( ~ ( isIndSet @ A )
      | ~ ( A @ B )
      | ( A @ ( s @ B ) ) ),
    inference(cnf,[status(esa)],[57]) ).

thf(18039,plain,
    ( ( ( ^ [A: $i] : ( isIndSet @ d ) )
     != ( ^ [A: $i] : $false ) )
    | ( ( isIndSet
        @ ^ [A: $i] : ( d @ sk71 ) )
     != ( isIndSet
        @ ^ [A: $i] : $true ) ) ),
    inference(paramod_ordered,[status(thm)],[70,10074]) ).

thf(18156,plain,
    ( ( ( ^ [A: $i] : ( isIndSet @ d ) )
     != ( ^ [A: $i] : $false ) )
    | ( ( ^ [A: $i] : ( d @ sk71 ) )
     != ( ^ [A: $i] : $true ) ) ),
    inference(simp,[status(thm)],[18039]) ).

thf(5623,plain,
    ( ( ( isIndSet
        @ ^ [A: $i] :
            ( isIndSet
            @ ^ [B: $i] :
                ( isIndSet
                @ ^ [C: $i] :
                    ( isIndSet
                    @ ^ [D: $i] :
                      ! [E: $i] :
                        ( ( d @ ( s @ E ) )
                       => ( d @ ( s @ ( s @ E ) ) ) ) ) ) ) )
      = ( isIndSet
        @ ^ [A: $i] : ( d @ ( s @ A ) ) ) )
    | ( ( isIndSet
        @ ^ [A: $i] : ( d @ ( s @ A ) ) )
     != ( isIndSet
        @ ^ [A: $i] : ( d @ ( s @ A ) ) ) ) ),
    inference(paramod_ordered,[status(thm)],[3363,2219]) ).

thf(5624,plain,
    ( ( isIndSet
      @ ^ [A: $i] :
          ( isIndSet
          @ ^ [B: $i] :
              ( isIndSet
              @ ^ [C: $i] :
                  ( isIndSet
                  @ ^ [D: $i] :
                    ! [E: $i] :
                      ( ( d @ ( s @ E ) )
                     => ( d @ ( s @ ( s @ E ) ) ) ) ) ) ) )
    = ( isIndSet
      @ ^ [A: $i] : ( d @ ( s @ A ) ) ) ),
    inference(pattern_uni,[status(thm)],[5623:[]]) ).

thf(14032,plain,
    ( ( isIndSet
      @ ^ [A: $i] :
          ( isIndSet
          @ ^ [B: $i] :
              ( isIndSet
              @ ^ [C: $i] :
                ! [D: $i] :
                  ( ( d @ ( s @ D ) )
                 => ( d @ ( s @ ( s @ D ) ) ) ) ) ) )
    = ( isIndSet
      @ ^ [A: $i] : ( d @ ( s @ A ) ) ) ),
    inference(rewrite,[status(thm)],[5624,3053]) ).

thf(15220,plain,
    ( ( isIndSet
      @ ^ [A: $i] :
          ( isIndSet
          @ ^ [B: $i] :
            ! [C: $i] :
              ( ( d @ ( s @ C ) )
             => ( d @ ( s @ ( s @ C ) ) ) ) ) )
    = ( isIndSet
      @ ^ [A: $i] : ( d @ ( s @ A ) ) ) ),
    inference(rewrite,[status(thm)],[14032,3053]) ).

thf(15239,plain,
    ( ( ( isIndSet
        @ ^ [A: $i] :
            ( isIndSet
            @ ^ [B: $i] :
                ( isIndSet
                @ ^ [C: $i] :
                    ( isIndSet
                    @ ^ [D: $i] :
                      ! [E: $i] :
                        ( ( d @ ( s @ E ) )
                       => ( d @ ( s @ ( s @ E ) ) ) ) ) ) ) )
      = ( isIndSet
        @ ^ [A: $i] : ( d @ ( s @ A ) ) ) )
    | ( ( isIndSet
        @ ^ [A: $i] : ( d @ ( s @ A ) ) )
     != ( isIndSet
        @ ^ [A: $i] : ( d @ ( s @ A ) ) ) ) ),
    inference(paramod_ordered,[status(thm)],[15220,5793]) ).

thf(15240,plain,
    ( ( isIndSet
      @ ^ [A: $i] :
          ( isIndSet
          @ ^ [B: $i] :
              ( isIndSet
              @ ^ [C: $i] :
                  ( isIndSet
                  @ ^ [D: $i] :
                    ! [E: $i] :
                      ( ( d @ ( s @ E ) )
                     => ( d @ ( s @ ( s @ E ) ) ) ) ) ) ) )
    = ( isIndSet
      @ ^ [A: $i] : ( d @ ( s @ A ) ) ) ),
    inference(pattern_uni,[status(thm)],[15239:[]]) ).

thf(15966,plain,
    ( ( isIndSet
      @ ^ [A: $i] :
          ( isIndSet
          @ ^ [B: $i] :
              ( isIndSet
              @ ^ [C: $i] :
                ! [D: $i] :
                  ( ( d @ ( s @ D ) )
                 => ( d @ ( s @ ( s @ D ) ) ) ) ) ) )
    = ( isIndSet
      @ ^ [A: $i] : ( d @ ( s @ A ) ) ) ),
    inference(rewrite,[status(thm)],[15240,3053]) ).

thf(101,plain,
    ! [C: $i,B: $i,A: $i] :
      ( ( ( f @ B @ ( f @ ( s @ B ) @ C ) )
        = ( s @ e ) )
      | ( ( f @ A @ e )
       != ( f @ ( s @ B ) @ ( s @ C ) ) ) ),
    inference(paramod_ordered,[status(thm)],[13,19]) ).

thf(104,plain,
    ! [C: $i,B: $i,A: $i] :
      ( ( ( f @ B @ ( f @ ( s @ B ) @ C ) )
        = ( s @ e ) )
      | ( A
       != ( s @ B ) )
      | ( ( s @ C )
       != e ) ),
    inference(simp,[status(thm)],[101]) ).

thf(108,plain,
    ! [B: $i,A: $i] :
      ( ( ( f @ A @ ( f @ ( s @ A ) @ B ) )
        = ( s @ e ) )
      | ( ( s @ B )
       != e ) ),
    inference(simp,[status(thm)],[104]) ).

thf(25506,plain,
    ( ( ( ^ [A: $i] : ( d @ ( s @ A ) ) )
     != ( ^ [A: $i] : $false ) )
    | ( ( d @ sk91 )
     != ( d @ e ) ) ),
    inference(paramod_ordered,[status(thm)],[20,25461]) ).

thf(25533,plain,
    ( ( ( ^ [A: $i] : ( d @ ( s @ A ) ) )
     != ( ^ [A: $i] : $false ) )
    | ( sk91 != e ) ),
    inference(simp,[status(thm)],[25506]) ).

thf(8817,plain,
    ( ( ( ^ [A: $i] : ( isIndSet @ d ) )
     != ( ^ [A: $i] : $false ) )
    | ( ( d @ ( s @ sk68 ) )
     != ( d @ e ) ) ),
    inference(paramod_ordered,[status(thm)],[20,2479]) ).

thf(8885,plain,
    ( ( ( ^ [A: $i] : ( isIndSet @ d ) )
     != ( ^ [A: $i] : $false ) )
    | ( ( s @ sk68 )
     != e ) ),
    inference(simp,[status(thm)],[8817]) ).

thf(6105,plain,
    ! [A: $i > $o] :
      ( ( isIndSet @ d )
      | ( ( ! [B: $i] :
              ( ( A @ B )
             => ( A @ ( s @ B ) ) ) )
        = ( isIndSet @ A ) )
      | ( ( d @ ( sk1 @ d ) )
       != ( A @ e ) ) ),
    inference(paramod_ordered,[status(thm)],[1391,27]) ).

thf(6186,plain,
    ( ( isIndSet @ d )
    | ( ( ! [A: $i] :
            ( ( d @ ( sk1 @ d ) )
           => ( d @ ( sk1 @ d ) ) ) )
      = ( isIndSet
        @ ^ [A: $i] : ( d @ ( sk1 @ d ) ) ) ) ),
    inference(pre_uni,[status(thm)],[6105:[bind(A,$thf( ^ [B: $i] : ( d @ ( sk1 @ d ) ) ))]]) ).

thf(6202,plain,
    ( ( isIndSet @ d )
    | ( isIndSet
      @ ^ [A: $i] : ( d @ ( sk1 @ d ) ) ) ),
    inference(simp,[status(thm)],[6186]) ).

thf(10714,plain,
    ( ( ( isIndSet
        @ ^ [A: $i] :
            ( isIndSet
            @ ^ [B: $i] :
                ( isIndSet
                @ ^ [C: $i] :
                    ( isIndSet
                    @ ^ [D: $i] :
                        ( isIndSet
                        @ ^ [E: $i] :
                            ( isIndSet
                            @ ^ [F: $i] :
                              ! [G: $i] :
                                ( ( d @ ( s @ G ) )
                               => ( d @ ( s @ ( s @ G ) ) ) ) ) ) ) ) ) )
      = ( isIndSet
        @ ^ [A: $i] : ( d @ ( s @ A ) ) ) )
    | ( ( isIndSet
        @ ^ [A: $i] : ( d @ ( s @ A ) ) )
     != ( isIndSet
        @ ^ [A: $i] : ( d @ ( s @ A ) ) ) ) ),
    inference(paramod_ordered,[status(thm)],[5624,5793]) ).

thf(10715,plain,
    ( ( isIndSet
      @ ^ [A: $i] :
          ( isIndSet
          @ ^ [B: $i] :
              ( isIndSet
              @ ^ [C: $i] :
                  ( isIndSet
                  @ ^ [D: $i] :
                      ( isIndSet
                      @ ^ [E: $i] :
                          ( isIndSet
                          @ ^ [F: $i] :
                            ! [G: $i] :
                              ( ( d @ ( s @ G ) )
                             => ( d @ ( s @ ( s @ G ) ) ) ) ) ) ) ) ) )
    = ( isIndSet
      @ ^ [A: $i] : ( d @ ( s @ A ) ) ) ),
    inference(pattern_uni,[status(thm)],[10714:[]]) ).

thf(26009,plain,
    ( ( isIndSet
      @ ^ [A: $i] :
          ( isIndSet
          @ ^ [B: $i] :
              ( isIndSet
              @ ^ [C: $i] :
                  ( isIndSet
                  @ ^ [D: $i] :
                      ( isIndSet
                      @ ^ [E: $i] :
                        ! [F: $i] :
                          ( ( d @ ( s @ F ) )
                         => ( d @ ( s @ ( s @ F ) ) ) ) ) ) ) ) )
    = ( isIndSet
      @ ^ [A: $i] : ( d @ ( s @ A ) ) ) ),
    inference(rewrite,[status(thm)],[10715,3053]) ).

thf(26551,plain,
    ( ( ( isIndSet
        @ ^ [A: $i] :
            ( isIndSet
            @ ^ [B: $i] :
                ( isIndSet
                @ ^ [C: $i] :
                    ( isIndSet
                    @ ^ [D: $i] :
                        ( isIndSet
                        @ ^ [E: $i] :
                            ( isIndSet
                            @ ^ [F: $i] : ( d @ ( s @ F ) ) ) ) ) ) ) )
      = ( isIndSet
        @ ^ [A: $i] : ( d @ ( s @ A ) ) ) )
    | ( ( ! [A: $i] :
            ( ( d @ ( s @ A ) )
           => ( d @ ( s @ ( s @ A ) ) ) ) )
     != ( ! [A: $i] :
            ( ( d @ ( s @ A ) )
           => ( d @ ( s @ ( s @ A ) ) ) ) ) ) ),
    inference(paramod_ordered,[status(thm)],[2485,26009]) ).

thf(26552,plain,
    ( ( isIndSet
      @ ^ [A: $i] :
          ( isIndSet
          @ ^ [B: $i] :
              ( isIndSet
              @ ^ [C: $i] :
                  ( isIndSet
                  @ ^ [D: $i] :
                      ( isIndSet
                      @ ^ [E: $i] :
                          ( isIndSet
                          @ ^ [F: $i] : ( d @ ( s @ F ) ) ) ) ) ) ) )
    = ( isIndSet
      @ ^ [A: $i] : ( d @ ( s @ A ) ) ) ),
    inference(pattern_uni,[status(thm)],[26551:[]]) ).

thf(27235,plain,
    ( ( isIndSet
      @ ^ [A: $i] :
          ( isIndSet
          @ ^ [B: $i] :
              ( isIndSet
              @ ^ [C: $i] :
                  ( isIndSet
                  @ ^ [D: $i] : ( d @ ( s @ D ) ) ) ) ) )
    = ( isIndSet
      @ ^ [A: $i] : ( d @ ( s @ A ) ) ) ),
    inference(rewrite,[status(thm)],[26552,5793]) ).

thf(20450,plain,
    ! [A: $i > $o] :
      ( ( ( ! [B: $i > $o] :
              ( ( isIndSet @ B )
             => ( B @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) ) ) ) ) ) ) )
          & ! [B: $i] :
              ( ( A @ B )
             => ( A @ ( s @ B ) ) ) )
        = ( isIndSet @ A ) )
      | ( ( p @ e @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) )
       != ( A @ e ) ) ),
    inference(paramod_ordered,[status(thm)],[19843,27]) ).

thf(20515,plain,
    ( ( ! [A: $i > $o] :
          ( ( isIndSet @ A )
         => ( A @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) ) ) ) ) ) ) )
      & ! [A: $i] :
          ( ( p @ e @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) )
         => ( p @ e @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) ) ) )
    = ( isIndSet
      @ ^ [A: $i] : ( p @ e @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) ) ) ),
    inference(pre_uni,[status(thm)],[20450:[bind(A,$thf( ^ [B: $i] : ( p @ e @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) ) ))]]) ).

thf(20580,plain,
    ( ( ! [A: $i > $o] :
          ( ( isIndSet @ A )
         => ( A @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) ) ) ) ) ) ) ) )
    = ( isIndSet
      @ ^ [A: $i] : ( p @ e @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) ) ) ),
    inference(simp,[status(thm)],[20515]) ).

thf(23321,plain,
    ( ( isIndSet
      @ ^ [A: $i] :
        ! [B: $i > $o] :
          ( ( isIndSet @ B )
         => ( B @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) ) ) ) ) ) ) ) )
    = ( ! [A: $i > $o] :
          ( ( isIndSet @ A )
         => ( A @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) ) ) ) ) ) ) ) ) ),
    inference(rewrite,[status(thm)],[20580,19843]) ).

thf(6040,plain,
    ( ( d
     != ( ^ [A: $i] : $false ) )
    | ( ( d @ ( s @ e ) )
     != ( d @ sk2 ) ) ),
    inference(paramod_ordered,[status(thm)],[250,4512]) ).

thf(6051,plain,
    ( ( d
     != ( ^ [A: $i] : $false ) )
    | ( ( s @ e )
     != sk2 ) ),
    inference(simp,[status(thm)],[6040]) ).

thf(20825,plain,
    ( ( ( ^ [A: $i] : ( isIndSet @ d ) )
     != ( ^ [A: $i] : $false ) )
    | ( ( isIndSet
        @ ^ [A: $i] : ( d @ sk2 ) )
     != ( isIndSet
        @ ^ [A: $i] : $true ) ) ),
    inference(paramod_ordered,[status(thm)],[70,13115]) ).

thf(20951,plain,
    ( ( ( ^ [A: $i] : ( isIndSet @ d ) )
     != ( ^ [A: $i] : $false ) )
    | ( ( ^ [A: $i] : ( d @ sk2 ) )
     != ( ^ [A: $i] : $true ) ) ),
    inference(simp,[status(thm)],[20825]) ).

thf(30,plain,
    ( d @ ( f @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) ) )
 != ( d @ e ),
    inference(paramod_ordered,[status(thm)],[20,10]) ).

thf(32,plain,
    ( f @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) )
 != e,
    inference(simp,[status(thm)],[30]) ).

thf(99,plain,
    ( f @ ( s @ ( s @ ( s @ e ) ) ) @ ( f @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) @ ( s @ ( s @ ( s @ e ) ) ) ) )
 != e,
    inference(rewrite,[status(thm)],[32,19]) ).

thf(199,plain,
    ( f @ ( s @ ( s @ ( s @ e ) ) ) @ ( f @ ( s @ ( s @ ( s @ e ) ) ) @ ( f @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) @ ( s @ ( s @ e ) ) ) ) )
 != e,
    inference(rewrite,[status(thm)],[99,19]) ).

thf(2991,plain,
    ! [A: $i > $o] :
      ( ~ ( isIndSet @ A )
      | ( d
       != ( ^ [B: $i] : $false ) )
      | ( ( A @ e )
       != ( d @ ( s @ sk69 ) ) ) ),
    inference(paramod_ordered,[status(thm)],[67,2481]) ).

thf(3007,plain,
    ( ~ ( isIndSet
        @ ^ [A: $i] : ( d @ ( s @ sk69 ) ) )
    | ( d
     != ( ^ [A: $i] : $false ) ) ),
    inference(pre_uni,[status(thm)],[2991:[bind(A,$thf( ^ [B: $i] : ( d @ ( s @ sk69 ) ) ))]]) ).

thf(11355,plain,
    ( ( d
     != ( ^ [A: $i] : $false ) )
    | ( ( isIndSet
        @ ^ [A: $i] : ( d @ ( s @ sk69 ) ) )
     != ( isIndSet
        @ ^ [A: $i] : $true ) ) ),
    inference(paramod_ordered,[status(thm)],[70,3007]) ).

thf(11429,plain,
    ( ( d
     != ( ^ [A: $i] : $false ) )
    | ( ( ^ [A: $i] : ( d @ ( s @ sk69 ) ) )
     != ( ^ [A: $i] : $true ) ) ),
    inference(simp,[status(thm)],[11355]) ).

thf(3458,plain,
    ( ( d
     != ( ^ [A: $i] : $false ) )
    | ( ( d @ sk69 )
     != ( d @ e ) ) ),
    inference(paramod_ordered,[status(thm)],[20,2989]) ).

thf(3475,plain,
    ( ( d
     != ( ^ [A: $i] : $false ) )
    | ( sk69 != e ) ),
    inference(simp,[status(thm)],[3458]) ).

thf(3658,plain,
    ( ( ! [A: $i > $o] :
          ( ( isIndSet @ A )
         => ( A @ ( s @ ( s @ ( s @ e ) ) ) ) )
      & ! [A: $i] :
          ( ( p @ e @ ( s @ e ) )
         => ( p @ e @ ( s @ e ) ) ) )
    = ( isIndSet
      @ ^ [A: $i] : ( p @ e @ ( s @ e ) ) ) ),
    inference(pre_uni,[status(thm)],[3653:[bind(A,$thf( ^ [B: $i] : ( p @ e @ ( s @ e ) ) ))]]) ).

thf(3692,plain,
    ( ( ! [A: $i > $o] :
          ( ( isIndSet @ A )
         => ( A @ ( s @ ( s @ ( s @ e ) ) ) ) ) )
    = ( isIndSet
      @ ^ [A: $i] : ( p @ e @ ( s @ e ) ) ) ),
    inference(simp,[status(thm)],[3658]) ).

thf(4117,plain,
    ( ( isIndSet
      @ ^ [A: $i] :
        ! [B: $i > $o] :
          ( ( isIndSet @ B )
         => ( B @ ( s @ ( s @ ( s @ e ) ) ) ) ) )
    = ( ! [A: $i > $o] :
          ( ( isIndSet @ A )
         => ( A @ ( s @ ( s @ ( s @ e ) ) ) ) ) ) ),
    inference(rewrite,[status(thm)],[3692,3494]) ).

thf(1115,plain,
    ( ( isIndSet
      @ ^ [A: $i] : ( isIndSet @ d ) )
    | ~ ! [A: $i] :
          ( ( d @ A )
         => ( d @ ( s @ A ) ) ) ),
    inference(bool_ext,[status(thm)],[1086]) ).

thf(1166,plain,
    ( ( d @ sk9 )
    | ( isIndSet
      @ ^ [A: $i] : ( isIndSet @ d ) ) ),
    inference(cnf,[status(esa)],[1115]) ).

thf(1257,plain,
    ( ( d @ sk9 )
    | ( isIndSet @ d ) ),
    inference(rewrite,[status(thm)],[1166,1119]) ).

thf(5888,plain,
    ( ( ( isIndSet
        @ ^ [A: $i] :
            ( isIndSet
            @ ^ [B: $i] :
                ( isIndSet
                @ ^ [C: $i] :
                    ( isIndSet
                    @ ^ [D: $i] :
                        ( isIndSet
                        @ ^ [E: $i] :
                          ! [F: $i] :
                            ( ( d @ ( s @ F ) )
                           => ( d @ ( s @ ( s @ F ) ) ) ) ) ) ) ) )
      = ( isIndSet
        @ ^ [A: $i] : ( d @ ( s @ A ) ) ) )
    | ( ( isIndSet
        @ ^ [A: $i] : ( d @ ( s @ A ) ) )
     != ( isIndSet
        @ ^ [A: $i] : ( d @ ( s @ A ) ) ) ) ),
    inference(paramod_ordered,[status(thm)],[3363,5793]) ).

thf(5889,plain,
    ( ( isIndSet
      @ ^ [A: $i] :
          ( isIndSet
          @ ^ [B: $i] :
              ( isIndSet
              @ ^ [C: $i] :
                  ( isIndSet
                  @ ^ [D: $i] :
                      ( isIndSet
                      @ ^ [E: $i] :
                        ! [F: $i] :
                          ( ( d @ ( s @ F ) )
                         => ( d @ ( s @ ( s @ F ) ) ) ) ) ) ) ) )
    = ( isIndSet
      @ ^ [A: $i] : ( d @ ( s @ A ) ) ) ),
    inference(pattern_uni,[status(thm)],[5888:[]]) ).

thf(17215,plain,
    ( ( isIndSet
      @ ^ [A: $i] :
          ( isIndSet
          @ ^ [B: $i] :
              ( isIndSet
              @ ^ [C: $i] :
                  ( isIndSet
                  @ ^ [D: $i] :
                    ! [E: $i] :
                      ( ( d @ ( s @ E ) )
                     => ( d @ ( s @ ( s @ E ) ) ) ) ) ) ) )
    = ( isIndSet
      @ ^ [A: $i] : ( d @ ( s @ A ) ) ) ),
    inference(rewrite,[status(thm)],[5889,3053]) ).

thf(9911,plain,
    ( ( ( ^ [A: $i] : ( isIndSet @ d ) )
     != ( ^ [A: $i] : $false ) )
    | ( ( d @ ( s @ sk71 ) )
     != ( d @ e ) ) ),
    inference(paramod_ordered,[status(thm)],[20,2629]) ).

thf(9966,plain,
    ( ( ( ^ [A: $i] : ( isIndSet @ d ) )
     != ( ^ [A: $i] : $false ) )
    | ( ( s @ sk71 )
     != e ) ),
    inference(simp,[status(thm)],[9911]) ).

thf(114,plain,
    ( ( isIndSet @ d )
    | ~ ( isIndSet
        @ ^ [A: $i] :
          ! [B: $i] :
            ( ( d @ B )
           => ( d @ ( s @ B ) ) ) ) ),
    inference(bool_ext,[status(thm)],[94]) ).

thf(9626,plain,
    ( ( isIndSet @ d )
    | ~ ! [A: $i] :
          ( ( d @ A )
         => ( d @ ( s @ A ) ) ) ),
    inference(rewrite,[status(thm)],[114,112]) ).

thf(9628,plain,
    ( ( d @ sk211 )
    | ( isIndSet @ d ) ),
    inference(cnf,[status(esa)],[9626]) ).

thf(1493,plain,
    ( ( isIndSet
      @ ^ [A: $i] : ( isIndSet @ d ) )
    | ~ ! [A: $i] :
          ( ( d @ A )
         => ( d @ ( s @ A ) ) ) ),
    inference(bool_ext,[status(thm)],[1491]) ).

thf(1584,plain,
    ( ( d @ sk23 )
    | ( isIndSet
      @ ^ [A: $i] : ( isIndSet @ d ) ) ),
    inference(cnf,[status(esa)],[1493]) ).

thf(7547,plain,
    ( ( d @ sk23 )
    | ( isIndSet @ d ) ),
    inference(rewrite,[status(thm)],[1584,1119]) ).

thf(2271,plain,
    ! [A: $i > $o] :
      ( ~ ! [B: $i] :
            ( ( d @ B )
           => ( d @ ( s @ B ) ) )
      | ( A @ e )
      | ( ( isIndSet
          @ ^ [B: $i] : ( isIndSet @ d ) )
       != ( isIndSet @ A ) ) ),
    inference(paramod_ordered,[status(thm)],[1491,67]) ).

thf(2272,plain,
    ( ~ ! [A: $i] :
          ( ( d @ A )
         => ( d @ ( s @ A ) ) )
    | ( isIndSet @ d ) ),
    inference(pattern_uni,[status(thm)],[2271:[bind(A,$thf( ^ [B: $i] : ( isIndSet @ d ) ))]]) ).

thf(2443,plain,
    ( ( isIndSet @ d )
    | ( d @ sk66 ) ),
    inference(cnf,[status(esa)],[2272]) ).

thf(3644,plain,
    ! [B: $i,A: $i] :
      ( ( ( ! [C: $i > $o] :
              ( ( isIndSet @ C )
             => ( C @ ( f @ A @ B ) ) ) )
        = ( ! [C: $i > $o] :
              ( ( isIndSet @ C )
             => ( C @ ( s @ ( s @ ( s @ e ) ) ) ) ) ) )
      | ( ( p @ e @ ( s @ e ) )
       != ( p @ A @ B ) ) ),
    inference(paramod_ordered,[status(thm)],[3494,29]) ).

thf(3645,plain,
    ( ( ! [A: $i > $o] :
          ( ( isIndSet @ A )
         => ( A @ ( f @ e @ ( s @ e ) ) ) ) )
    = ( ! [A: $i > $o] :
          ( ( isIndSet @ A )
         => ( A @ ( s @ ( s @ ( s @ e ) ) ) ) ) ) ),
    inference(pattern_uni,[status(thm)],[3644:[bind(A,$thf( e )),bind(B,$thf( s @ e ))]]) ).

thf(3864,plain,
    ( ( ! [A: $i > $o] :
          ( ( isIndSet @ A )
         => ( A @ ( s @ ( s @ ( f @ e @ e ) ) ) ) ) )
    = ( ! [A: $i > $o] :
          ( ( isIndSet @ A )
         => ( A @ ( s @ ( s @ ( s @ e ) ) ) ) ) ) ),
    inference(rewrite,[status(thm)],[3645,16]) ).

thf(13896,plain,
    ( ( d
     != ( ^ [A: $i] : $false ) )
    | ( ( isIndSet
        @ ^ [A: $i] : ( d @ ( s @ sk2 ) ) )
     != ( isIndSet
        @ ^ [A: $i] : $true ) ) ),
    inference(paramod_ordered,[status(thm)],[70,4535]) ).

thf(13969,plain,
    ( ( d
     != ( ^ [A: $i] : $false ) )
    | ( ( ^ [A: $i] : ( d @ ( s @ sk2 ) ) )
     != ( ^ [A: $i] : $true ) ) ),
    inference(simp,[status(thm)],[13896]) ).

thf(2792,plain,
    ( ~ ! [A: $i] :
          ( ( d @ ( s @ A ) )
         => ( d @ ( s @ ( s @ A ) ) ) )
    | ( isIndSet
      @ ^ [A: $i] : ( d @ ( s @ A ) ) ) ),
    inference(bool_ext,[status(thm)],[2485]) ).

thf(2934,plain,
    ( ( isIndSet
      @ ^ [A: $i] : ( d @ ( s @ A ) ) )
    | ( d @ ( s @ sk94 ) ) ),
    inference(cnf,[status(esa)],[2792]) ).

thf(11895,plain,
    ! [B: $i,A: $i] :
      ( ( ( p @ e @ ( s @ ( s @ ( s @ B ) ) ) )
        = ( ! [C: $i > $o] :
              ( ( isIndSet @ C )
             => ( C @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) ) ) ) ) ) ) )
      | ( ( f @ A @ e )
       != ( f @ e @ B ) ) ),
    inference(paramod_ordered,[status(thm)],[13,7433]) ).

thf(11896,plain,
    ( ( p @ e @ ( s @ ( s @ ( s @ e ) ) ) )
    = ( ! [A: $i > $o] :
          ( ( isIndSet @ A )
         => ( A @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) ) ) ) ) ) ) ),
    inference(pattern_uni,[status(thm)],[11895:[bind(A,$thf( e )),bind(B,$thf( e ))]]) ).

thf(12450,plain,
    ! [A: $i > $o] :
      ( ( ( ! [B: $i > $o] :
              ( ( isIndSet @ B )
             => ( B @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) ) ) ) ) )
          & ! [B: $i] :
              ( ( A @ B )
             => ( A @ ( s @ B ) ) ) )
        = ( isIndSet @ A ) )
      | ( ( p @ e @ ( s @ ( s @ ( s @ e ) ) ) )
       != ( A @ e ) ) ),
    inference(paramod_ordered,[status(thm)],[11896,27]) ).

thf(12483,plain,
    ( ( ! [A: $i > $o] :
          ( ( isIndSet @ A )
         => ( A @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) ) ) ) ) )
      & ! [A: $i] :
          ( ( p @ e @ ( s @ ( s @ ( s @ e ) ) ) )
         => ( p @ e @ ( s @ ( s @ ( s @ e ) ) ) ) ) )
    = ( isIndSet
      @ ^ [A: $i] : ( p @ e @ ( s @ ( s @ ( s @ e ) ) ) ) ) ),
    inference(pre_uni,[status(thm)],[12450:[bind(A,$thf( ^ [B: $i] : ( p @ e @ ( s @ ( s @ ( s @ e ) ) ) ) ))]]) ).

thf(12551,plain,
    ( ( ! [A: $i > $o] :
          ( ( isIndSet @ A )
         => ( A @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) ) ) ) ) ) )
    = ( isIndSet
      @ ^ [A: $i] : ( p @ e @ ( s @ ( s @ ( s @ e ) ) ) ) ) ),
    inference(simp,[status(thm)],[12483]) ).

thf(13193,plain,
    ( ( isIndSet
      @ ^ [A: $i] :
        ! [B: $i > $o] :
          ( ( isIndSet @ B )
         => ( B @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) ) ) ) ) ) )
    = ( ! [A: $i > $o] :
          ( ( isIndSet @ A )
         => ( A @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) ) ) ) ) ) ) ),
    inference(rewrite,[status(thm)],[12551,11896]) ).

thf(286,plain,
    ! [A: $i > $o] :
      ( ( ( ! [B: $i] :
              ( ( A @ B )
             => ( A @ ( s @ B ) ) ) )
        = ( isIndSet @ A ) )
      | ( ( d @ ( s @ ( s @ ( s @ e ) ) ) )
       != ( A @ e ) ) ),
    inference(paramod_ordered,[status(thm)],[274,27]) ).

thf(290,plain,
    ( ( ! [A: $i] :
          ( ( d @ ( s @ ( s @ ( s @ A ) ) ) )
         => ( d @ ( s @ ( s @ ( s @ ( s @ A ) ) ) ) ) ) )
    = ( isIndSet
      @ ^ [A: $i] : ( d @ ( s @ ( s @ ( s @ A ) ) ) ) ) ),
    inference(pre_uni,[status(thm)],[286:[bind(A,$thf( ^ [B: $i] : ( d @ ( s @ ( s @ ( s @ B ) ) ) ) ))]]) ).

thf(6030,plain,
    ( ( d
     != ( ^ [A: $i] : $false ) )
    | ( ( d @ sk2 )
     != ( d @ e ) ) ),
    inference(paramod_ordered,[status(thm)],[20,4512]) ).

thf(6050,plain,
    ( ( d
     != ( ^ [A: $i] : $false ) )
    | ( sk2 != e ) ),
    inference(simp,[status(thm)],[6030]) ).

thf(163,plain,
    ! [A: $i] :
      ( ~ ( d @ ( f @ ( s @ ( s @ ( s @ e ) ) ) @ ( f @ ( s @ ( s @ ( s @ e ) ) ) @ ( s @ e ) ) ) )
      | ( ( f @ A @ e )
       != ( f @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) @ ( s @ ( s @ e ) ) ) ) ),
    inference(paramod_ordered,[status(thm)],[13,162]) ).

thf(182,plain,
    ! [A: $i] :
      ( ~ ( d @ ( f @ ( s @ ( s @ ( s @ e ) ) ) @ ( f @ ( s @ ( s @ ( s @ e ) ) ) @ ( s @ e ) ) ) )
      | ( A
       != ( s @ ( s @ ( s @ ( s @ e ) ) ) ) )
      | ( ( s @ ( s @ e ) )
       != e ) ),
    inference(simp,[status(thm)],[163]) ).

thf(183,plain,
    ( ~ ( d @ ( f @ ( s @ ( s @ ( s @ e ) ) ) @ ( f @ ( s @ ( s @ ( s @ e ) ) ) @ ( s @ e ) ) ) )
    | ( ( s @ ( s @ e ) )
     != e ) ),
    inference(simp,[status(thm)],[182]) ).

thf(221,plain,
    ( ~ ( d @ ( f @ ( s @ ( s @ ( s @ e ) ) ) @ ( f @ ( s @ ( s @ e ) ) @ ( f @ ( s @ ( s @ ( s @ e ) ) ) @ e ) ) ) )
    | ( ( s @ ( s @ e ) )
     != e ) ),
    inference(rewrite,[status(thm)],[183,19]) ).

thf(222,plain,
    ! [A: $i] :
      ( ~ ( d @ ( f @ ( s @ ( s @ ( s @ e ) ) ) @ ( f @ ( s @ ( s @ e ) ) @ ( s @ e ) ) ) )
      | ( ( s @ ( s @ e ) )
       != e )
      | ( ( f @ A @ e )
       != ( f @ ( s @ ( s @ ( s @ e ) ) ) @ e ) ) ),
    inference(paramod_ordered,[status(thm)],[13,221]) ).

thf(223,plain,
    ( ~ ( d @ ( f @ ( s @ ( s @ ( s @ e ) ) ) @ ( f @ ( s @ ( s @ e ) ) @ ( s @ e ) ) ) )
    | ( ( s @ ( s @ e ) )
     != e ) ),
    inference(pattern_uni,[status(thm)],[222:[bind(A,$thf( s @ ( s @ ( s @ e ) ) ))]]) ).

thf(295,plain,
    ( ~ ( d @ ( f @ ( s @ ( s @ ( s @ e ) ) ) @ ( f @ ( s @ e ) @ ( f @ ( s @ ( s @ e ) ) @ e ) ) ) )
    | ( ( s @ ( s @ e ) )
     != e ) ),
    inference(rewrite,[status(thm)],[223,19]) ).

thf(297,plain,
    ! [A: $i] :
      ( ~ ( d @ ( f @ ( s @ ( s @ ( s @ e ) ) ) @ ( f @ ( s @ e ) @ ( s @ e ) ) ) )
      | ( ( s @ ( s @ e ) )
       != e )
      | ( ( f @ A @ e )
       != ( f @ ( s @ ( s @ e ) ) @ e ) ) ),
    inference(paramod_ordered,[status(thm)],[13,295]) ).

thf(298,plain,
    ( ~ ( d @ ( f @ ( s @ ( s @ ( s @ e ) ) ) @ ( f @ ( s @ e ) @ ( s @ e ) ) ) )
    | ( ( s @ ( s @ e ) )
     != e ) ),
    inference(pattern_uni,[status(thm)],[297:[bind(A,$thf( s @ ( s @ e ) ))]]) ).

thf(327,plain,
    ( ~ ( d @ ( f @ ( s @ ( s @ ( s @ e ) ) ) @ ( f @ e @ ( f @ ( s @ e ) @ e ) ) ) )
    | ( ( s @ ( s @ e ) )
     != e ) ),
    inference(rewrite,[status(thm)],[298,19]) ).

thf(330,plain,
    ! [A: $i] :
      ( ~ ( d @ ( f @ ( s @ ( s @ ( s @ e ) ) ) @ ( f @ e @ ( s @ e ) ) ) )
      | ( ( s @ ( s @ e ) )
       != e )
      | ( ( f @ A @ e )
       != ( f @ ( s @ e ) @ e ) ) ),
    inference(paramod_ordered,[status(thm)],[13,327]) ).

thf(331,plain,
    ( ~ ( d @ ( f @ ( s @ ( s @ ( s @ e ) ) ) @ ( f @ e @ ( s @ e ) ) ) )
    | ( ( s @ ( s @ e ) )
     != e ) ),
    inference(pattern_uni,[status(thm)],[330:[bind(A,$thf( s @ e ))]]) ).

thf(412,plain,
    ( ~ ( d @ ( f @ ( s @ ( s @ ( s @ e ) ) ) @ ( s @ ( s @ ( f @ e @ e ) ) ) ) )
    | ( ( s @ ( s @ e ) )
     != e ) ),
    inference(rewrite,[status(thm)],[331,16]) ).

thf(416,plain,
    ! [A: $i] :
      ( ~ ( d @ ( f @ ( s @ ( s @ ( s @ e ) ) ) @ ( s @ ( s @ ( s @ e ) ) ) ) )
      | ( ( s @ ( s @ e ) )
       != e )
      | ( ( f @ A @ e )
       != ( f @ e @ e ) ) ),
    inference(paramod_ordered,[status(thm)],[13,412]) ).

thf(417,plain,
    ( ~ ( d @ ( f @ ( s @ ( s @ ( s @ e ) ) ) @ ( s @ ( s @ ( s @ e ) ) ) ) )
    | ( ( s @ ( s @ e ) )
     != e ) ),
    inference(pattern_uni,[status(thm)],[416:[bind(A,$thf( e ))]]) ).

thf(846,plain,
    ( ~ ( d @ ( f @ ( s @ ( s @ e ) ) @ ( f @ ( s @ ( s @ ( s @ e ) ) ) @ ( s @ ( s @ e ) ) ) ) )
    | ( ( s @ ( s @ e ) )
     != e ) ),
    inference(rewrite,[status(thm)],[417,19]) ).

thf(848,plain,
    ! [A: $i] :
      ( ~ ( d @ ( f @ ( s @ ( s @ e ) ) @ ( s @ e ) ) )
      | ( ( s @ ( s @ e ) )
       != e )
      | ( ( f @ A @ e )
       != ( f @ ( s @ ( s @ ( s @ e ) ) ) @ ( s @ ( s @ e ) ) ) ) ),
    inference(paramod_ordered,[status(thm)],[13,846]) ).

thf(884,plain,
    ! [A: $i] :
      ( ~ ( d @ ( f @ ( s @ ( s @ e ) ) @ ( s @ e ) ) )
      | ( ( s @ ( s @ e ) )
       != e )
      | ( A
       != ( s @ ( s @ ( s @ e ) ) ) )
      | ( ( s @ ( s @ e ) )
       != e ) ),
    inference(simp,[status(thm)],[848]) ).

thf(899,plain,
    ( ~ ( d @ ( f @ ( s @ ( s @ e ) ) @ ( s @ e ) ) )
    | ( ( s @ ( s @ e ) )
     != e ) ),
    inference(simp,[status(thm)],[884]) ).

thf(900,plain,
    ( ~ ( d @ ( f @ ( s @ e ) @ ( f @ ( s @ ( s @ e ) ) @ e ) ) )
    | ( ( s @ ( s @ e ) )
     != e ) ),
    inference(rewrite,[status(thm)],[899,19]) ).

thf(902,plain,
    ! [A: $i] :
      ( ~ ( d @ ( f @ ( s @ e ) @ ( s @ e ) ) )
      | ( ( s @ ( s @ e ) )
       != e )
      | ( ( f @ A @ e )
       != ( f @ ( s @ ( s @ e ) ) @ e ) ) ),
    inference(paramod_ordered,[status(thm)],[13,900]) ).

thf(903,plain,
    ( ~ ( d @ ( f @ ( s @ e ) @ ( s @ e ) ) )
    | ( ( s @ ( s @ e ) )
     != e ) ),
    inference(pattern_uni,[status(thm)],[902:[bind(A,$thf( s @ ( s @ e ) ))]]) ).

thf(964,plain,
    ( ~ ( d @ ( f @ e @ ( f @ ( s @ e ) @ e ) ) )
    | ( ( s @ ( s @ e ) )
     != e ) ),
    inference(rewrite,[status(thm)],[903,19]) ).

thf(967,plain,
    ! [A: $i] :
      ( ~ ( d @ ( f @ e @ ( s @ e ) ) )
      | ( ( s @ ( s @ e ) )
       != e )
      | ( ( f @ A @ e )
       != ( f @ ( s @ e ) @ e ) ) ),
    inference(paramod_ordered,[status(thm)],[13,964]) ).

thf(968,plain,
    ( ~ ( d @ ( f @ e @ ( s @ e ) ) )
    | ( ( s @ ( s @ e ) )
     != e ) ),
    inference(pattern_uni,[status(thm)],[967:[bind(A,$thf( s @ e ))]]) ).

thf(1005,plain,
    ( ~ ( d @ ( s @ ( s @ ( f @ e @ e ) ) ) )
    | ( ( s @ ( s @ e ) )
     != e ) ),
    inference(rewrite,[status(thm)],[968,16]) ).

thf(1007,plain,
    ! [A: $i] :
      ( ~ ( d @ ( s @ ( s @ ( s @ e ) ) ) )
      | ( ( s @ ( s @ e ) )
       != e )
      | ( ( f @ A @ e )
       != ( f @ e @ e ) ) ),
    inference(paramod_ordered,[status(thm)],[13,1005]) ).

thf(1008,plain,
    ( ~ ( d @ ( s @ ( s @ ( s @ e ) ) ) )
    | ( ( s @ ( s @ e ) )
     != e ) ),
    inference(pattern_uni,[status(thm)],[1007:[bind(A,$thf( e ))]]) ).

thf(1171,plain,
    ( ~ $true
    | ( ( s @ ( s @ e ) )
     != e ) ),
    inference(rewrite,[status(thm)],[1008,274]) ).

thf(1172,plain,
    ( s @ ( s @ e ) )
 != e,
    inference(simp,[status(thm)],[1171]) ).

thf(7779,plain,
    ! [B: $i,A: $i] :
      ( ( ( s @ B )
       != e )
      | ~ ( d @ ( f @ ( s @ ( s @ ( s @ e ) ) ) @ ( s @ e ) ) )
      | ( ( f @ A @ ( f @ ( s @ A ) @ B ) )
       != ( f @ ( s @ ( s @ ( s @ e ) ) ) @ ( f @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) @ ( s @ ( s @ e ) ) ) ) ) ),
    inference(paramod_ordered,[status(thm)],[108,162]) ).

thf(7780,plain,
    ( ( ( s @ ( s @ ( s @ e ) ) )
     != e )
    | ~ ( d @ ( f @ ( s @ ( s @ ( s @ e ) ) ) @ ( s @ e ) ) ) ),
    inference(pattern_uni,[status(thm)],[7779:[bind(A,$thf( s @ ( s @ ( s @ e ) ) )),bind(B,$thf( s @ ( s @ e ) ))]]) ).

thf(8352,plain,
    ( ( ( s @ ( s @ ( s @ e ) ) )
     != e )
    | ~ ( d @ ( f @ ( s @ ( s @ e ) ) @ ( f @ ( s @ ( s @ ( s @ e ) ) ) @ e ) ) ) ),
    inference(rewrite,[status(thm)],[7780,19]) ).

thf(8354,plain,
    ! [A: $i] :
      ( ( ( s @ ( s @ ( s @ e ) ) )
       != e )
      | ~ ( d @ ( f @ ( s @ ( s @ e ) ) @ ( s @ e ) ) )
      | ( ( f @ A @ e )
       != ( f @ ( s @ ( s @ ( s @ e ) ) ) @ e ) ) ),
    inference(paramod_ordered,[status(thm)],[13,8352]) ).

thf(8355,plain,
    ( ( ( s @ ( s @ ( s @ e ) ) )
     != e )
    | ~ ( d @ ( f @ ( s @ ( s @ e ) ) @ ( s @ e ) ) ) ),
    inference(pattern_uni,[status(thm)],[8354:[bind(A,$thf( s @ ( s @ ( s @ e ) ) ))]]) ).

thf(8991,plain,
    ( ( ( s @ ( s @ ( s @ e ) ) )
     != e )
    | ~ ( d @ ( f @ ( s @ e ) @ ( f @ ( s @ ( s @ e ) ) @ e ) ) ) ),
    inference(rewrite,[status(thm)],[8355,19]) ).

thf(8993,plain,
    ! [A: $i] :
      ( ( ( s @ ( s @ ( s @ e ) ) )
       != e )
      | ~ ( d @ ( f @ ( s @ e ) @ ( s @ e ) ) )
      | ( ( f @ A @ e )
       != ( f @ ( s @ ( s @ e ) ) @ e ) ) ),
    inference(paramod_ordered,[status(thm)],[13,8991]) ).

thf(8994,plain,
    ( ( ( s @ ( s @ ( s @ e ) ) )
     != e )
    | ~ ( d @ ( f @ ( s @ e ) @ ( s @ e ) ) ) ),
    inference(pattern_uni,[status(thm)],[8993:[bind(A,$thf( s @ ( s @ e ) ))]]) ).

thf(9146,plain,
    ( ( ( s @ ( s @ ( s @ e ) ) )
     != e )
    | ~ ( d @ ( f @ e @ ( f @ ( s @ e ) @ e ) ) ) ),
    inference(rewrite,[status(thm)],[8994,19]) ).

thf(9149,plain,
    ! [A: $i] :
      ( ( ( s @ ( s @ ( s @ e ) ) )
       != e )
      | ~ ( d @ ( f @ e @ ( s @ e ) ) )
      | ( ( f @ A @ e )
       != ( f @ ( s @ e ) @ e ) ) ),
    inference(paramod_ordered,[status(thm)],[13,9146]) ).

thf(9150,plain,
    ( ( ( s @ ( s @ ( s @ e ) ) )
     != e )
    | ~ ( d @ ( f @ e @ ( s @ e ) ) ) ),
    inference(pattern_uni,[status(thm)],[9149:[bind(A,$thf( s @ e ))]]) ).

thf(9455,plain,
    ( ( ( s @ ( s @ ( s @ e ) ) )
     != e )
    | ~ ( d @ ( s @ ( s @ ( f @ e @ e ) ) ) ) ),
    inference(rewrite,[status(thm)],[9150,16]) ).

thf(9457,plain,
    ! [A: $i] :
      ( ( ( s @ ( s @ ( s @ e ) ) )
       != e )
      | ~ ( d @ ( s @ ( s @ ( s @ e ) ) ) )
      | ( ( f @ A @ e )
       != ( f @ e @ e ) ) ),
    inference(paramod_ordered,[status(thm)],[13,9455]) ).

thf(9458,plain,
    ( ( ( s @ ( s @ ( s @ e ) ) )
     != e )
    | ~ ( d @ ( s @ ( s @ ( s @ e ) ) ) ) ),
    inference(pattern_uni,[status(thm)],[9457:[bind(A,$thf( e ))]]) ).

thf(9582,plain,
    ( ( ( s @ ( s @ ( s @ e ) ) )
     != e )
    | ~ $true ),
    inference(rewrite,[status(thm)],[9458,274]) ).

thf(9583,plain,
    ( s @ ( s @ ( s @ e ) ) )
 != e,
    inference(simp,[status(thm)],[9582]) ).

thf(3467,plain,
    ( ( d
     != ( ^ [A: $i] : $false ) )
    | ( ( d @ ( s @ e ) )
     != ( d @ sk69 ) ) ),
    inference(paramod_ordered,[status(thm)],[250,2989]) ).

thf(3474,plain,
    ( ( d
     != ( ^ [A: $i] : $false ) )
    | ( ( s @ e )
     != sk69 ) ),
    inference(simp,[status(thm)],[3467]) ).

thf(33054,plain,
    $false,
    inference(e,[status(thm)],[69,3962,3053,479,2921,31391,7285,5793,10314,25494,24995,10,385,28317,13115,3481,1391,24,13552,25,14,4524,8967,25384,28448,2403,20,10074,8543,2989,78,29,4018,14423,106,6054,806,13719,10538,1119,23814,3955,6103,8289,6047,12350,12927,13104,381,260,28,70,4091,21,3471,14958,2560,2958,2464,65,28019,25534,285,3482,4512,30832,1111,8984,3001,12974,12179,27016,96,13,24149,4535,105,13103,22415,2995,14997,21023,21800,8290,264,15923,64,17,21400,819,10068,22,27,4526,3002,49,19843,11618,10083,7983,274,362,18570,27925,2625,25529,66,18156,15966,108,1044,2481,25533,19293,162,112,2629,8885,6202,27235,23321,9631,6051,20951,25461,3209,15220,67,199,9281,16,11429,3475,2219,4117,1257,17215,11,9930,3007,8982,250,9686,450,2479,9966,9628,7547,2443,3864,26,13969,23,2934,1491,13193,290,8837,6050,19,7433,26009,1172,400,9583,5354,3494,3570,2485,3474,11896]) ).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.22  % Problem  : theBenchmark.p : TPTP v0.0.0. Released v0.0.0.
% 0.13/0.24  % Command  : run_Leo-III %s %d
% 0.15/0.45  % Computer : n007.cluster.edu
% 0.15/0.45  % Model    : x86_64 x86_64
% 0.15/0.45  % CPU      : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.45  % Memory   : 8042.1875MB
% 0.15/0.45  % OS       : Linux 3.10.0-693.el7.x86_64
% 0.15/0.45  % CPULimit : 300
% 0.15/0.45  % WCLimit  : 300
% 0.15/0.45  % DateTime : Mon Aug  1 10:11:36 EDT 2022
% 0.15/0.45  % CPUTime  : 
% 1.06/1.11  % [INFO] 	 Parsing problem /export/starexec/sandbox/benchmark/theBenchmark.p ... 
% 1.43/1.26  % [INFO] 	 Parsing done (149ms). 
% 1.43/1.27  % [INFO] 	 Running in sequential loop mode. 
% 1.84/1.60  % [INFO] 	 eprover registered as external prover. 
% 1.84/1.60  % [INFO] 	 cvc4 registered as external prover. 
% 1.84/1.61  % [INFO] 	 Scanning for conjecture ... 
% 2.05/1.69  % [INFO] 	 Found a conjecture and 7 axioms. Running axiom selection ... 
% 2.05/1.72  % [INFO] 	 Axiom selection finished. Selected 7 axioms (removed 0 axioms). 
% 2.22/1.74  % [INFO] 	 Problem is higher-order (TPTP THF). 
% 2.22/1.75  % [INFO] 	 Type checking passed. 
% 2.22/1.75  % [CONFIG] 	 Using configuration: timeout(300) with strategy<name(default),share(1.0),primSubst(3),sos(false),unifierCount(4),uniDepth(8),boolExt(true),choice(true),renaming(true),funcspec(false), domConstr(0),specialInstances(39),restrictUniAttempts(true),termOrdering(CPO)>.  Searching for refutation ... 
% 230.96/49.63  % External prover 'e' found a proof!
% 230.96/49.63  % [INFO] 	 Killing All external provers ... 
% 230.96/49.63  % Time passed: 49027ms (effective reasoning time: 48354ms)
% 230.96/49.63  % Solved by strategy<name(default),share(1.0),primSubst(3),sos(false),unifierCount(4),uniDepth(8),boolExt(true),choice(true),renaming(true),funcspec(false), domConstr(0),specialInstances(39),restrictUniAttempts(true),termOrdering(CPO)>
% 230.96/49.63  % Axioms used in derivation (7): a5, a1, a2, p_def, a4, isIndSet_def, a3
% 230.96/49.63  % No. of inferences in proof: 474
% 230.96/49.63  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p : 49027 ms resp. 48354 ms w/o parsing
% 231.48/49.79  % SZS output start Refutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% See solution above
% 231.48/49.79  % [INFO] 	 Killing All external provers ... 
%------------------------------------------------------------------------------
