
module onehot_detect #(parameter int N = 4) (
    input  logic [N-1:0] vec_in       ,
    output logic         exactly_one  ,
    output logic         more_than_one
);


    localparam int NODES = 2**$clog2(N)-1;
    localparam int EDGES = 2*NODES + 1   ; //+1: zero'th is output

    logic[EDGES-1:0]        h, z, f;
    logic[2**$clog2(N)-1:0]  vec_in_ext;

    genvar i;
    generate
        for (i=0; i<2**$clog2(N); i++) begin: for_i
            if (i < N) begin
                assign vec_in_ext[i] = vec_in[i];
            end else begin
                assign vec_in_ext[i] = 1'b0;
            end
        end
    endgenerate

    genvar l;
    generate
        for (l=0; l<EDGES; l++) begin: for_l
            if (l >= NODES) begin: if_leaf
                // Initialize H, Z, F
                assign h[l] = vec_in_ext[l-NODES];
                assign z[l] = ~vec_in_ext[l-NODES];
                assign f[l] = 1'b0;
            end else begin: if_rest
                // check node:
                // H = (H_L  & Z_R) | (H_R & Z_L)
                assign h[l] = ( h[2*l+1] & z[2*l+2] ) | ( h[2*l+2] & z[2*l+1] );
                // Z = Z_L & Z_R
                assign z[l] = z[2*l+1] & z[2*l+2];
                // F = F_L | F_R | (H_L & H_R)
                assign f[l] = f[2*l+1] | f[2*l+2] | ( h[2*l+1] & h[2*l+2] );
            end
        end
    endgenerate
    assign exactly_one   = h[0];
    assign more_than_one = f[0];

endmodule