It often helps to read into the subtext of tecnical documents.
what was the goal?
did they fail at an amitous project, but have some takeawys that where then dressed up?

subtlety and subtext have no place in good technical writing.
I will then be explicit in what I wanted but and did not accomplish.

In a field full of "first steps", what is the destination?

nucluer fussion happens when the correct quatities of of uthwise unremarkable meterials are brought into contact.
A chain ratcion forms as atoms split and release release enrgetic particles that cuase more atoms to split.

I view the potential of Curry howard the same way.
Two larges communitees of programmers and mathemeticains work in nearly the same systems, to nearly the same ends.
they have each refined a taggering array of tools and teqniques that would be invaluable if made convienint for the other.

While this sounds utopian, the value will only be achieved when it is mundane.
I hope for a future where programmewrs are seen as slightly sloppy mathemeticans,
and mathemiticains are extreamely scrupoulus programers.
They will seen as more alike then different becuase they will be using the same tools in the same ecosystem.

% Right now rigor is ipractical for programmers that want it.
% while it is hard to make a formal proof for anyone, including mathemticians.

Python seems closest to this goal in the present day.
it is widely used in industry.
It is likely known by more mathemeticans than formal proof systems.

Python makes a number of compromises for usability that PL reasurchers would do well to consider.
It is a deeply ineficient lanuguge, which is fine.  once a thing is popular it's speed will improve.
varaible scoping is quite complicated, yet recursion and even mutual recursion works well enough in practice
Python is allergic to hard restrictions, but convetions are strong and predictable.

Python is a tool for human communication that can also be run on a computer.

I came to gradschool wanting to make a dependently typed language as easy to use as python.
I bleive such a language would need 
* full-spectrum dependent types
* non-terminating recursion and a simplified view of universes
* data types
* runtime type direceted proof search
* an ergonoic, predicatable, and rigorous acounting of effects
* testing facilities (ideally as libraries that reuse existing constructs such as proof search)
* good IDE support (agda syle holes, mouse over type info, breakpoint debugging)

Compromises worth gettign there
* inefficent
* logically inconsitent

However, I did not achieve this.  This thesis presents a priliminary attempt.

You cannot do anything serous with dependent types without commitment to some notion of equality.
Chapters 2 and 3, discuss the best compromise I could see on the issue, though this turned out to be far more complex and time consuming then I had hoped.

possibly illogical programs should get warnings


Contact me