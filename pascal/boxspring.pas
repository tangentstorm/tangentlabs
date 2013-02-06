{$MODE OBJFPC;}

PROGRAM boxspring;
  { force directed box and arrow explorer }

CONST
  max_nodes : Integer = 100;
  
TYPE
  
  generic Point<T> = CLASS
    x, y: T;
  END;
  
  generic Rect<T> = cLASS
  PUBLIC    
    x, y, w, h :T;
  END;
  
  Node = CLASS
  PUBLIC
    pos, vel, tar : Rect<Integer>;
    color         : Integer;
  END;
  
  Group = List
    
VAR 
  springs : array[1..kMaxNodes][1..kMaxNodes] OF Real;
  nodes   : array[1..kMaxNodes] OF Node;

BEGIN
END.  

{
set up initial node velocities to (0,0)
 set up initial node positions randomly // make sure no 2 nodes are in exactly the same position
 loop
     total_kinetic_energy := 0 // running sum of total kinetic energy over all particles
     for each node
         net-force := (0, 0) // running sum of total force on this particular node
         
         for each other node
             net-force := net-force + Coulomb_repulsion( this_node, other_node )
         next node
         
         for each spring connected to this node
             net-force := net-force + Hooke_attraction( this_node, spring )
         next spring
         
         // without damping, it moves forever
         this_node.velocity := (this_node.velocity + timestep * net-force) * damping
         this_node.position := this_node.position + timestep * this_node.velocity
         total_kinetic_energy := total_kinetic_energy + this_node.mass * (this_node.velocity)^2
     next node
 until total_kinetic_energy is less than some small number  // the simulation has stopped   moving
}
