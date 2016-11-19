/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
/**
 *
 * @author vlad
 */
public class laba1 {

    /**
     * @param args the command line arguments
     */
    public static void main(String[] args) {
        for(int i = 0; i < args.length; i++){
        
        	try{
                    double a = Double.parseDouble(args[i]);    
                }
        	catch(Exception e){
                    System.out.println(args[i] + " = string :)");
                    continue;
        	}
                if(args[i].contains("."))
                {
                     System.out.println(args[i] + " = decimal:)");       
                }
                else
                {
                    System.out.println(args[i] + " = integer :)");     
                }
            
        }
    }
    
}
