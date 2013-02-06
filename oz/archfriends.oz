Date: Thu, 5 Oct 2000 00:26:53 -0400 (EDT)
From: Michal Wallace <sabren@manifestation.com>
To: dougedmunds@users.sourceforge.net
Subject: Logic Puzzles


Hey Doug!

I found your brownbuffalo site last night, and was really
impressed. I've always loved logic puzzles, and have often thought
about writing programs to solve them, but never knew how.. Thanks for
a great site! I'm hooked on constraints now. :)

I tried to download Eclipse, but didn't want to go through the hassle
of sending a fax and all that.. I found another language called Oz
(www.mozart-oz.org) that seems to map prety well to your solutions,
though... I managed to port your Arch Friends puzzle (and actually get
the right answer!) after only an hour or two of fiddling around..
(the Oz constraint tutorial helped a lot, too)

Thought you might want to see it.

Cheers,

- Michal
------------------------------------------------------------------------
www.manifestation.com  www.sabren.com  www.linkwatcher.com  www.zike.net
------------------------------------------------------------------------

% Oz program to solve ArchFriends Puzzle, based on:
% http://brownbuffalo.sourceforge.net/ArchFriendsSolve.html
%
% with help from:
% http://www.mozart-oz.org/documentation/fdt/node15.html
%
% and:
% http://www.mozart-oz.org/documentation/fdt/node23.html

declare ArchFriends
proc  {ArchFriends Root}
   Flats Espa Pumps Sandals % shoes
   Foot Heels Shoe Tootsies % stores
   Shoes Stores
in
   Shoes = [Flats Espa Pumps Sandals]
   Stores = [Foot Heels Shoe Tootsies]
   Root  = sol(flats:Flats espa:Espa pumps:Pumps sandals:Sandals
               foot:Foot heels:Heels shoe:Shoe tootsies:Tootsies)
   Root ::: 1#4
   {FD.distinct Shoes}
   {FD.distinct Stores}
   Foot =: 2
   Flats =: Heels
   Pumps + 1 \=: Tootsies
   Shoe + 2 =: Sandals
   {FD.distribute ff Root}
end

% This next line opens up a window showing the result.
% I think this is meant for debugging, but I don't yet
% know enough Oz to make it print out the results... :)

{Browse {SearchAll ArchFriends}}

