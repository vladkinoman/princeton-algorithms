{N >= 0}
	i, x := 0, 0;
{inv P: 0 <= i <= N & x = (N_j: 0 <= j < i: even(i) & odd(a[j]))}
{bound t: N - i}

	do i < N --> if even(i) & odd(a[i])  --> x, i := x + 1, i + 1
				   |!((even) & odd(a[i)) --> i := i + 1
				 fi
	od
	
{R: x = (N_j: 0 <= j < i: even(i) & odd(a[j]))}

1) Q ==> WP(I, P)

	N >= 0 ==> (i, x := 0, 0, 0 <= i <= N & x = (N_j: 0 <= j < i: even(i) & odd(a[j])))
	N >= 0 ==> 0 <= 0 & 0 <= N & 0 = (N_j: 0 <= j < 0: even(i) & odd(a[j]))
	N >= 0 ==> N >= 0 & 0 = 0
	N >= 0 ==> N >= 0
	TRUE // alpha ==> alpha

2) P & B ==> WP(S, P)

	P & i < N ==> WP(IF, P) // Возьмём консеквент импликации
	WP(IF, P) ==> domain(BB) & (B1 v B2) & (B1 ==> WP(S1, P)) & (B2 ==> WP(S2, P)) // domain(BB) ==> TRUE
	((even(i) & odd(a[i])) v (!((even) & odd(a[i)))) & (B1 ==> WP(S1, P)) & (B2 ==> WP(S2, P))
	//((even(i) & odd(a[i])) v (!((even) & odd(a[i)))) ==> TRUE по закону исключения третьего
	(even(i) & odd(a[i]))