/** 
 * @info Round Robin (RR) Arbiter
 * 
 * @author VLSI Lab, EE dept., Democritus University of Thrace
 * 
 * @brief Round Robin (RR) Arbiter. If current priority points to input i, then the request vector ('request')
 *        is checked in the following order: i->...->N-1->0->...->i-1
 *        Priority is updated using 'update_pri', under the following policy:
 *        When input i is currently being granted ('grant[i]' asserted) and  update_pri[i] is asserted,
 *        priority will be updated to point to input i+1 in the next cycle.
 *        'grant' is at-most-one-hot - 'anygrant' is the OR-reduced request vector
 *
 * @param N number of input requestors
 * @param PRI_RST starting priority after reset (points to that position, i.e. can have a value 0...N-1)
 */

//import noc_global::*;

module rr_arbiter
   #(parameter int N        = 2,
     parameter int PRI_RST  = 0)
    (input  logic           clk,
     input  logic           rst,
     input  logic[N-1:0]    request,
     output logic[N-1:0]    grant,
     output logic           anygnt,
     input  logic           update_pri);	 

localparam int S = $clog2(N);

// Internal priority register
logic[N-1:0] priority2;

// Priority propagate and ganerate signals
logic [N-1:0] g [S:0];
logic [N-1:0] p [S-1:0];

logic [N-1:0] grant_s;
logic valid;

assign grant = grant_s;
	 
// Parallel prefix round-robin arbitration

int i,j;
always_comb
begin
   // initialize priority propagate 
   // and generate vectors
   p[0][0] = ~request[N-1];
   g[0][0] = priority2[0];
   for(j=1; j < N; j=j+1)
   begin
      p[0][j] = ~request[j-1];
      g[0][j] = priority2[j];
   end

   // implement first log2n-1 prefix levels
   for(i=1; i < S; i=i+1)
      for(j=0; j < N; j=j+1)
	  begin
	     if ((j-2**(i-1)) < 0)
		 begin
             g[i][j] = g[i-1][j] | ( p[i-1][j] & g[i-1][N+j-2**(i-1)]);
             p[i][j] = p[i-1][j] & p[i-1][N+j-2**(i-1)];
         end
         else
         begin
            g[i][j] = g[i-1][j] | ( p[i-1][j] & g[i-1][ j-2**(i-1)]);
            p[i][j] = p[i-1][j] & p[i-1][ j-2**(i-1)];
         end
      end

   // last prefix level
   for(j=0; j < N; j=j+1)
   begin
      if ((j-2**(S-1)) < 0)
         g[S][j] = g[S-1][j] | ( p[S-1][j] & g[S-1][ N+j-2**(S-1)]);
      else
         g[S][j] = g[S-1][j] | ( p[S-1][j] & g[S-1][ j-2**(S-1)]);
   end

   // grant signal generation 
   for(j=0; j < N; j=j+1)
      grant_s[j] = request[j] & g[S][j];

end

// Any grant generation at last prefix level
assign valid = ~( p[S-1][N-1] & p[S-1][N/2-1]);
assign anygnt = valid;

////////////////////////
// Priority update logic
////////////////////////
// int k;
always_ff @ (posedge clk, posedge rst)
begin
   if (rst) 
    priority2 <= (1'b1 << PRI_RST);
   else
      if (valid) // At least one input was granted 
      begin
         priority2 <= 0;
         for (int k=0; k < N; k=k+1)
           if (grant_s[k])
		      if (update_pri)
			  begin
			     if (k == (N-1))
				    priority2[0] <= 1'b1;
                 else
				    priority2[k+1] <= 1'b1;
               end
			   else
			      // if connection kept, current winner has the highest priority2
			      priority2[k] <= 1'b1; 
           		   
      end
end

endmodule
