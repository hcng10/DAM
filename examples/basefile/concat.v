module concat
(

);

    reg [31:0] s;
    wire [31:0] o;
    
    assign o = {1'b1, s[30:0]};
    
endmodule
