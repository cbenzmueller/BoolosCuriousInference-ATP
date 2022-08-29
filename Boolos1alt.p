% Declarations
thf(e_decl,type, e: $i ).
thf(s_decl,type, s: $i > $i ).
thf(d_decl,type, d: $i > $o ).
thf(f_decl,type, f: $i > $i > $i ).

% Auxiliary declarations
thf(ind_decl,type, ind: ( $i > $o ) > $o ).
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

% Shorthand notations   
thf(ind_def,definition,
    ! [Q: $i > $o] :
      ( ( ind @ Q )
      = ( ( Q @ e )
        & ! [X: $i] :
            ( ( Q @ X )
           => ( Q @ ( s @ X ) ) ) ) ) ).
  
thf(p_def,definition,
    ! [X: $i,Y: $i] :
      ( ( p @ X @ Y )
      = ( ^ [Z: $i] : ( ! [Q: $i > $o] :
            ( ( ind @ Q )
           => ( Q @ Z ) ) ) @ ( f @ X @ Y ) ) ) ).

% Conjecture 
thf(conj_0,conjecture,
    d @ ( f @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) @ ( s @ ( s @ ( s @ ( s @ e ) ) ) ) ) ).
