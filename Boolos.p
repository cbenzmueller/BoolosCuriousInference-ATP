% Declarations
thf(e_decl,type, e: $i ).
thf(s_decl,type, s: $i > $i ).
thf(d_decl,type, d: $i > $o ).
thf(f_decl,type, f: $i > $i > $i ).

% Auxiliary declarations
thf(p_decl,type, p: $i > $i > $o ).

% Axioms 
thf(a1,axiom,
    ! [N: $i] :
      ( ( f @ N @ e )
      = ( s @ e ) ) ).
thf(a2,axiom,
    ! [Y: $i] :
      ( ( f @ e @ ( s @ Y ) )
      = ( s @ ( s @ ( f @ e @ Y ) ) ) ) ).
thf(a3,axiom,
    ! [X: $i,Y: $i] :
      ( ( f @ ( s @ X ) @ ( s @ Y ) )
      = ( f @ X @ ( f @ ( s @ X ) @ Y ) ) ) ).
thf(a4,axiom,
    d @ e ).
thf(a5,axiom,
    ! [X: $i] :
      ( ( d @ X )
     => ( d @ ( s @ X ) ) ) ).

% Shorthand notation p as comprehension instance 
thf(p_def,axiom,
      ( p
      = ( ^ [X: $i,Y: $i] :
            ( ^ [X2: $i] :
              ! [X3: $i > $o] :
                ( ( ^ [Q: $i > $o] :
                      ( ( Q @ e )
                      & ! [X: $i] :
                          ( ( Q @ X )
                         => ( Q @ ( s @ X ) ) ) )
                  @ X3 )
               => ( X3 @ X2 ) )
            @ ( f @ X @ Y ) ) ) ) ).

% conjecture
thf(conj_0,conjecture,
    d @ ( f @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) ) ).
