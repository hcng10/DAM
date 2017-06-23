module partselect
(

);

    reg [31:0] s;
    wire [28:0] o;
    
    assign o = s[28:0];
    
endmodule
