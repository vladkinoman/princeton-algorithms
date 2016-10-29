//////// sumTo ////////
function sumTo(n) {
	var s = 0;
	for (var i = 1; i <= n; i++) {
		s += i;
	}
	return s;
}

function sumTo(n) {
	return (n != 1) ? n + sumTo(n - 1) : n;
}

// the fastest example -> without recursion and cycle
function sumTo(n) {
	return ((1 + n) * n) / 2;
}

///////// fact /////////
function fact(n) {
	return (n != 1) ? n * fact(n - 1) : 1; 
}

///////// fibo /////////
function fib(n) {
	return (n > 1) ? fib(n - 1) + fib(n - 2) : n;
}
// for fib(77) function will generate many inner calls