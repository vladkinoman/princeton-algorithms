# the program finds amount of numbers in sequence which 
# are located at even places and which are odd numbers

def count(N, a):
	K = 0 # number of 
	i = 0
	while i<N:
		if i%2 != 0 and a[i]%2 != 0:
			K = K + 1
		i = i + 1
	return K

# TODO: exceptions