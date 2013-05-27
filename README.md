BOBJ
====

[BOBJ](http://cseweb.ucsd.edu/groups/tatami/bobj/) is a system for prototyping and algebraic 
specification and verification built by [Kai Lin](klin@cs.ucsd.edu) following the ideas of
[Joseph Goguen](mailto:goguen@cs.ucsd.edu). BOBJ is part of the [Tatami Projekt](http://cseweb.ucsd.edu/groups/tatami/)
at UCSD.

This repository is a fork of the publicly available BOBJ system
at 

[ftp://ftp.cs.ucsd.edu/pub/fac/goguen/bobj](ftp://ftp.cs.ucsd.edu/pub/fac/goguen/bobj) (last modified 2006-02)

intended to be both, a mirror and also a place for system actualization.

BOBJ's home page can be found at

[http://cseweb.ucsd.edu/groups/tatami/bobj/](http://cseweb.ucsd.edu/groups/tatami/bobj/).

OBJ is actually a family of algebraic specification and verification systems which
most prominent members are [OBJ3](http://cseweb.ucsd.edu/~goguen/sys/obj.html#OBJ3), [CafeOBJ](http://cseweb.ucsd.edu/~goguen/sys/obj.html#CafeOBJ), 
and [BOBJ](http://cseweb.ucsd.edu/~goguen/sys/obj.html#BOBJ). 

Please see the BOBJ [README](readme.html) file for more details.


Build instructions:
-------------------

Compile BOBJ:

    mvn clean package

Run BOBJ:

    java -jar target/bobj-0.9.jar
