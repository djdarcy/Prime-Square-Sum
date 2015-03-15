# Prime-Square-Sum
There is a brief notebook that outlines the concept available in the "paper and notes" folder: [Triangular Numbers and Squared Primes.nb](https://raw.githubusercontent.com/djdarcy/Prime-Square-Sum/master/paper%20and%20notes/2010%20-%20Recurrence%20relation%20between%20triangular%20numbers%20and%20squared%20primes%20-%20D.%20Darcy.nb). 

To view the notebook you will need a full version of Mathematica or the [CDF Player](http://www.wolfram.com/cdf-player/).

The python program squares primes and sums them together to determine if:

```
stf(b) = sum_(z=1)^qg(b) tf(b,z);
```

is equal to the series of squared primes.

```
b = triangular number (also the number base);              //equal to: (z^2+z)/2 
r = qg(b) = size of the base row of the triangular number; //qg(b) = 1/2(-1+sqrt(1+8b)
z = row in the triangular number;  //ex. tf(10,4)=0123; tf(10,3)=456; tf(10,2)=78, etc.)
```

Where tf() is defined to be:

![tf(b,z) = (-2 + 2b - 2b^2 + z - bz - z^2 + bz^2 + b^z(2 + 2b^2 + z + z^2 - b(2 + z + z^2))) / (2(-1 + b)^2)](/paper%20and%20notes/function-tf-defined.png?raw=true "tf defined")

There is an interesting relationship when `{b=10, r=4}` where the sum of the rows in base-10, `0123 + 456 + 78 + 9`, happens to work out to be the sum of the first seven squared primes.

```
stf(10) = 2² + 3² + 5² + 7² + 11² + 13² + 17² = 666
```

What I find fascinating about this relationship is the resultant value 666 is a triangular number itself. So the question then is if we were able to sum the rows of a 666 element triangle with 36 rows in base-666 would the result _also_ be the sum of squared primes?

This program attempts to provide an answer. The base-10 number from `stf(666)` is massively large unfortunately at 98 digits:

`37005443752611483714216385166550857181329086284892731078593232926279977894581784762614450464857290`

So I'll probably have to adapt it at some point to work with CUDA or OpenCL to see if I can speed up the computations. I have a large series of primes precomputed for people to speed up the operation.

[Prime numbers in text format](http://www.4shared.com/archive/OZQrNbMice/txt-primes.html)

[Prime numbers in dat format](http://www.4shared.com/archive/mG7fTed6ce/dat-primes.html)


