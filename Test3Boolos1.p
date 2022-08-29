% Declarations
thf(e_decl,type, e: $i ).
thf(s_decl,type, s: $i > $i ).
thf(d_decl,type, d: $i > $o ).
thf(f_decl,type, f: $i > $i > $i ).

thf(ind_decl,type, ind: ( $i > $o ) > $o ).
thf(p_decl,type, p: $i > $i > $o ).

% Shorthand notations  
thf(ind_def,axiom,
    ( ind
    = ( ^ [Q: $i > $o] :
          ( ( Q @ e )
          & ! [X: $i] :
              ( ( Q @ X )
             => ( Q @ ( s @ X ) ) ) ) ) ) ).

% Conjecture 
thf(conj_0,conjecture,
    (![X: $i, Y: $i]:  ?[Q: $i > $o]:
      ( ((Q @ (f @ X @ Y)) => (p @ X @ Y))
        &
        ((ind @ Q)|(p @ X @ Y))
    ))).
