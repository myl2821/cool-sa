

#include <stdlib.h>
#include <stdio.h>
#include <stdarg.h>
#include "semant.h"
#include "utilities.h"


extern int semant_debug;            /* debug flag */
extern char *curr_filename;         /* will be used in cgen */


//////////////////////////////////////////////////////////////////////
//
// Symbols
//
// For convenience, a large number of symbols are predefined here.
// These symbols include the primitive type and method names, as well
// as fixed names used by the runtime system.
//
//////////////////////////////////////////////////////////////////////
static Symbol 
    arg,
    arg2,
    Bool,
    concat,
    cool_abort,
    copy,
    Int,
    in_int,
    in_string,
    IO,
    length,
    Main,
    main_meth,
    No_class,
    No_type,
    Object,
    out_int,
    out_string,
    prim_slot,
    self,
    SELF_TYPE,
    Str,
    str_field,
    substr,
    type_name,
    val;
//
// Initializing the predefined symbols.
//
static void initialize_constants(void)
{
    arg         = idtable.add_string("arg");
    arg2        = idtable.add_string("arg2");
    Bool        = idtable.add_string("Bool");
    concat      = idtable.add_string("concat");
    cool_abort  = idtable.add_string("abort");
    copy        = idtable.add_string("copy");
    Int         = idtable.add_string("Int");
    in_int      = idtable.add_string("in_int");
    in_string   = idtable.add_string("in_string");
    IO          = idtable.add_string("IO");
    length      = idtable.add_string("length");
    Main        = idtable.add_string("Main");
    main_meth   = idtable.add_string("main");
    //   _no_class is a symbol that can't be the name of any 
    //   user-defined class.
    No_class    = idtable.add_string("_no_class");
    No_type     = idtable.add_string("_no_type");
    Object      = idtable.add_string("Object");
    out_int     = idtable.add_string("out_int");
    out_string  = idtable.add_string("out_string");
    prim_slot   = idtable.add_string("_prim_slot");
    self        = idtable.add_string("self");
    SELF_TYPE   = idtable.add_string("SELF_TYPE");
    Str         = idtable.add_string("String");
    str_field   = idtable.add_string("_str_field");
    substr      = idtable.add_string("substr");
    type_name   = idtable.add_string("type_name");
    val         = idtable.add_string("_val");
}


/* the WHOLE AST will be build in this constructor */
ClassTable::ClassTable(Classes classes) : semant_errors(0) , error_stream(cerr) {

    class_symtable.enterscope();
    install_basic_classes();

    Symbol class_name;
    c_node current_class; 
    // Do some check in the first loop, build class symbol table
    for ( int i = classes->first(); classes->more(i); i = classes->next(i) ) {

        current_class = (c_node)classes->nth(i);
        class_name = current_class->get_name();

        if( class_symtable.lookup(class_name) != NULL ){
            //  check the situation of class multiply defined. 
            ostream& os =  semant_error(current_class);
            os << "Class " << class_name << " was previously defined." << endl;
            continue;
        } 


        class_symtable.addid(class_name,current_class);
    }
    // first scan, not related to expression
    for( int i = classes->first(); classes->more(i); i = classes->next(i) ){
        current_class = (c_node)classes->nth(i);
        semant_class(current_class);
    }

    //check Main 
    if ( class_symtable.probe(Main) == NULL){
        ostream& os =  semant_error();
        os << "Class  main is not defined." << endl;
    }

    else {
        c_node main_class = (c_node)class_symtable.probe(Main);
        Table main_table = main_class->featureTable;
        // must do this probe after semant_class
        if ( main_table.probe(main_meth) == NULL ){ 
            ostream& os =  semant_error(main_class);
            os << "no 'main' method in class Main." << endl;
        }

    }


    // second scan, check expression
    for( int i = classes->first(); classes->more(i); i = classes->next(i) ){
        current_class = (c_node)classes->nth(i);
        semant_class_attr(current_class);
    }


    class_symtable.exitscope();
}

// first scan
void ClassTable::semant_class(c_node current_class){

    Table current_table = current_class->featureTable;
    current_table.enterscope();

    Symbol class_name = current_class->get_name();
    Symbol parent_name;

    if ( class_name != Object ){
        parent_name = current_class->get_parent();

        if ( parent_name == Bool || parent_name == SELF_TYPE || parent_name == Str){
            ostream& os =  semant_error(current_class);
            os << "Class " << class_name << " cannot inherit from class " << parent_name << "." << endl;
        }

        else if ( class_symtable.lookup(parent_name) == NULL ){
            ostream& os =  semant_error(current_class);
            os << "Class " << class_name << " inherits from an undefined class " << parent_name << "." << endl;
        }
    }

    Features features = current_class->get_features();

    for( int i = features->first(); features->more(i); i = features->next(i) ){
        Feature feature = features->nth(i);
        if ( feature->get_type() == attrType ){
            semant_attr( current_class, (attr_class*)feature );         
        }
        else if ( feature-> get_type() == methodType ){
            semant_method( current_class, (method_class*)feature );       
        }
    } 


}


// second scan
void ClassTable::semant_class_attr(c_node current_class){

    Table current_table = current_class->featureTable;

    Symbol class_name = current_class->get_name();
    Symbol parent_name;
    Features features = current_class->get_features();

    for( int i = features->first(); features->more(i); i = features->next(i) ){
        Feature feature = features->nth(i);
        if ( feature->get_type() == attrType ){
            semant_attr_expr( current_class, (attr_class*)feature );         
        }
        else if ( feature-> get_type() == methodType ){
            semant_method_expr( current_class, (method_class*)feature );       
        }
    } 

}


// First scan
void ClassTable::semant_attr(c_node current_class,attr_class* attr){
    Symbol attr_name = attr->get_name();
    Table current_table = current_class->featureTable;
    Symbol attr_type = attr->get_type_decl();

    if( class_symtable.lookup(attr_type) == NULL){
        ostream& os = semant_error(current_class);
        os << "attribute " << attr_name << " declared with undefined type " << attr_type << endl;
    }

    if ( attr_name == self ){
        ostream& os = semant_error(current_class);
        os << "Cannot assign to 'self'." << endl;
    }
    
    else if ( current_table.probe(attr_name) ){
        ostream& os = semant_error(current_class);
        os << "attribute " << attr_name << " is multiply defined " << endl;
    }

    current_table.addid(attr_name,attr);

}

// First scan
void ClassTable::semant_method(c_node current_class,method_class* method){
    Symbol method_name = method->get_name();
    Table current_table = current_class->featureTable;
    Symbol ret_type = method->get_return_type();
    Formals formals = method->get_formals();
    Expression expr = method->get_expr();

    if( class_symtable.lookup(ret_type) == NULL){
        ostream& os = semant_error(current_class);
        os << "method " << method_name << " return undefined type " << ret_type << endl;
    }

    if ( current_table.probe(method_name) ){
        ostream& os = semant_error(current_class);
        os << "method " << method_name << " is multiply defined " << endl;
    }


    current_table.addid(method_name,method);
}

// second scan
void ClassTable::semant_attr_expr(c_node current_class,attr_class* attr){
    Symbol attr_name = attr->get_name();
    Table current_table = current_class->featureTable;
    Symbol attr_type = attr->get_type_decl();
    Expression init = attr->get_init();
    semant_expr(current_class, init);

    if ( check_parent(attr_type , init->type) == false ){
        ostream& os = semant_error(current_class);
        os << "expression type " << init->type <<" must conform to attribution type " << attr_type << "." << endl; 
    }
    
}

// second scan
void ClassTable::semant_method_expr(c_node current_class,method_class* method){
    Formals formals = method->get_formals();
    Symbol ret_type = method->get_return_type();
    Table current_table = current_class->featureTable;
    current_table.enterscope();
    for( int i = formals->first(); formals->more(i); i = formals->next(i) ){
        Formal f = formals->nth(i);
        semant_formal(current_class,f);
    }
    current_table.exitscope();
    Expression expr = method->get_expr();
    semant_expr(current_class,expr);

    if ( check_parent(ret_type , expr->type) == false ){
        ostream& os = semant_error(current_class);
        os << "expression type " << expr->type <<" must conform to return type " << ret_type << "." << endl; 
    }
    
}



void ClassTable::semant_formal(c_node current_class,Formal f){
    Table current_table = current_class->featureTable;
    formal_class * formal = (formal_class*) f;
    
    if (formal->get_name() == self){
        ostream& os = semant_error(current_class);
        os << "'self' as a formal identifier." <<endl; 
    
    }

    else if(current_table.probe(formal->get_name() ) ){
        ostream& os = semant_error(current_class);
        os << "formal " << formal->get_name() << "was defined previously." <<endl; 
    }
    
    if(formal->get_type_decl() == SELF_TYPE){
        ostream& os = semant_error(current_class);
        os << "SELF_TYPE as a formal type.\n";
    }

    else if(class_symtable.lookup(formal->get_type_decl()) == NULL ) {
        ostream& os = semant_error(current_class);
        os << "formal " << formal->get_name() << "has undefined type " << formal->get_type_decl() << "." << endl; 
    }
    current_table.addid(formal->get_name(), formal);
}

void ClassTable::semant_expr(c_node current_class,Expression expr){

    expr->type = No_type; // for error handle

    switch (expr->get_type()){
        case assignType:
            {
                break;
            }
        case static_dispatchType:
            {
                break;
            }
        case dispatchType:
            {
                break;
            }
        case condType:
            {
                break;
            }
        case loopType:
            {
                break;
            }
        case caseType:
            {
                break;
            }
        case blockType:
            {
                break;
            }
        case letType:
            {
                break;
            }
        case plusType:
            {
                plus_class* classptr = (plus_class*)expr;
                if( classptr->get_e1()->type == Int && classptr->get_e2()->type == Int){
                    expr->type = Int;
                }
                else {
                    ostream& os = semant_error(current_class);
                    os << "non-Int arguments: " << classptr->get_e1()->type << " + " << classptr->get_e2()->type << ".";
                }
                break;
            }
        case subType:
            {
                sub_class* classptr = (sub_class*)expr;
                if( classptr->get_e1()->type == Int && classptr->get_e2()->type == Int){
                    expr->type = Int;
                }
                else {
                    ostream& os = semant_error(current_class);
                    os << "non-Int arguments: " << classptr->get_e1()->type << " - " << classptr->get_e2()->type << ".";
                }
                break;
            }
        case mulType:
            {
                mul_class* classptr = (mul_class*)expr;
                if( classptr->get_e1()->type == Int && classptr->get_e2()->type == Int){
                    expr->type = Int;
                }
                else {
                    ostream& os = semant_error(current_class);
                    os << "non-Int arguments: " << classptr->get_e1()->type << " * " << classptr->get_e2()->type << ".";
                }
                break;
            }
        case divType:
            {
                divide_class* classptr = (divide_class*)expr;
                if( classptr->get_e1()->type == Int && classptr->get_e2()->type == Int){
                    expr->type = Int;
                }
                else {
                    ostream& os = semant_error(current_class);
                    os << "non-Int arguments: " << classptr->get_e1()->type << " + " << classptr->get_e2()->type << ".";
                }
                break;
            }
        case negType:
            {
                break;
            }
        case ltType:
            {
                break;
            }
        case eqType:
            {
                break;
            }
        case leqType:
            {
                break;
            }
        case int_constType:
            {
                expr->type = Int;
                break;
            }
        case bool_constType:
            {
                expr->type = Bool;
                break;
            }
        case string_constType:
            {
                expr->type = Str;
                break;
            }
        case newType:
            {
                break;
            }
        case isvoidType:
            {
                break;
            }
        case no_exprType:
            {
                expr->type = No_type;
                break;
            }
        case objectType:
            {
                expr->type = Object; 
                break;
            }

        default:
            break;
    }

}



/*
 *  subroutines that helps implement the semantic analysis
 *
 *  check_parent(Symbol parent, Symbol child) : check if inheritance exists
 * 
 *  lub (Symbol type1,Symbol type2) : find the least upper bound between two input types
 *
 */

bool ClassTable::check_parent(Symbol parent, Symbol child) {
    if ( parent == child || parent == Object || child == No_type ){
        return true;
    }

    while (child != No_class){
        c_node c = (c_node) class_symtable.lookup(child);
        if (c == NULL){
            return false;
        }
        child = c->get_parent();
        if (child == parent){
            return true;
        }
    }
    return false;
}

Symbol ClassTable::lub(Symbol type1,Symbol type2){
    if(check_parent(type1,type2) || type2 == No_type){
        return type1;
    }
    else if(check_parent(type2,type1) || type1 == No_type ){
        return type2;
    }

    else {
        c_node c = (c_node) class_symtable.lookup(type1);
        type1 = c->get_parent(); 
        return lub(type1,type2); 

    }


}



/*
 * subroutines end
 */


void ClassTable::install_basic_classes() {

    // The tree package uses these globals to annotate the classes built below.
    // curr_lineno  = 0;
    Symbol filename = stringtable.add_string("<basic class>");

    // The following demonstrates how to create dummy parse trees to
    // refer to basic Cool classes.  There's no need for method
    // bodies -- these are already built into the runtime system.

    // IMPORTANT: The results of the following expressions are
    // stored in local variables.  You will want to do something
    // with those variables at the end of this method to make this
    // code meaningful.

    // 
    // The Object class has no parent class. Its methods are
    //        abort() : Object    aborts the program
    //        type_name() : Str   returns a string representation of class name
    //        copy() : SELF_TYPE  returns a copy of the object
    //
    // There is no need for method bodies in the basic classes---these
    // are already built in to the runtime system.

    Class_ Object_class =
        class_(Object, 
                No_class,
                append_Features(
                    append_Features(
                        single_Features(method(cool_abort, nil_Formals(), Object, no_expr())),
                        single_Features(method(type_name, nil_Formals(), Str, no_expr()))),
                    single_Features(method(copy, nil_Formals(), SELF_TYPE, no_expr()))),
                filename);

    // 
    // The IO class inherits from Object. Its methods are
    //        out_string(Str) : SELF_TYPE       writes a string to the output
    //        out_int(Int) : SELF_TYPE            "    an int    "  "     "
    //        in_string() : Str                 reads a string from the input
    //        in_int() : Int                      "   an int     "  "     "
    //
    Class_ IO_class = 
        class_(IO, 
                Object,
                append_Features(
                    append_Features(
                        append_Features(
                            single_Features(method(out_string, single_Formals(formal(arg, Str)),
                                    SELF_TYPE, no_expr())),
                            single_Features(method(out_int, single_Formals(formal(arg, Int)),
                                    SELF_TYPE, no_expr()))),
                        single_Features(method(in_string, nil_Formals(), Str, no_expr()))),
                    single_Features(method(in_int, nil_Formals(), Int, no_expr()))),
                filename);  

    //
    // The Int class has no methods and only a single attribute, the
    // "val" for the integer. 
    //
    Class_ Int_class =
        class_(Int, 
                Object,
                single_Features(attr(val, prim_slot, no_expr())),
                filename);

    //
    // Bool also has only the "val" slot.
    //
    Class_ Bool_class =
        class_(Bool, Object, single_Features(attr(val, prim_slot, no_expr())),filename);

    //
    // The class Str has a number of slots and operations:
    //       val                                  the length of the string
    //       str_field                            the string itself
    //       length() : Int                       returns length of the string
    //       concat(arg: Str) : Str               performs string concatenation
    //       substr(arg: Int, arg2: Int): Str     substring selection
    //       
    Class_ Str_class =
        class_(Str, 
                Object,
                append_Features(
                    append_Features(
                        append_Features(
                            append_Features(
                                single_Features(attr(val, Int, no_expr())),
                                single_Features(attr(str_field, prim_slot, no_expr()))),
                            single_Features(method(length, nil_Formals(), Int, no_expr()))),
                        single_Features(method(concat, 
                                single_Formals(formal(arg, Str)),
                                Str, 
                                no_expr()))),
                    single_Features(method(substr, 
                            append_Formals(single_Formals(formal(arg, Int)), 
                                single_Formals(formal(arg2, Int))),
                            Str, 
                            no_expr()))),
                filename);

    // add primitive class into class table
    class_symtable.addid(Object,(class__class*)Object_class); 
    class_symtable.addid(IO,(class__class*)IO_class); 
    class_symtable.addid(Int,(class__class*)Int_class); 
    class_symtable.addid(Bool,(class__class*)Bool_class); 
    class_symtable.addid(Str,(class__class*)Str_class); 

}

////////////////////////////////////////////////////////////////////
//
// semant_error is an overloaded function for reporting errors
// during semantic analysis.  There are three versions:
//
//    ostream& ClassTable::semant_error()                
//
//    ostream& ClassTable::semant_error(Class_ c)
//       print line number and filename for `c'
//
//    ostream& ClassTable::semant_error(Symbol filename, tree_node *t)  
//       print a line number and filename
//
///////////////////////////////////////////////////////////////////

ostream& ClassTable::semant_error(Class_ c)
{                                                             
    return semant_error(c->get_filename(),c);
}    

ostream& ClassTable::semant_error(Symbol filename, tree_node *t)
{
    error_stream << filename << ":" << t->get_line_number() << ": ";
    return semant_error();
}

ostream& ClassTable::semant_error()                  
{                                                 
    semant_errors++;                            
    return error_stream;
} 



/*   This is the entry point to the semantic checker.

     Your checker should do the following two things:

     1) Check that the program is semantically correct
     2) Decorate the abstract syntax tree with type information
     by setting the `type' field in each Expression node.
     (see `tree.h')

     You are free to first do 1), make sure you catch all semantic
     errors. Part 2) can be done in a second stage, when you want
     to build mycoolc.
     */
void program_class::semant()
{
    initialize_constants();

    /* ClassTable constructor may do some semantic analysis */

    // the parameter 'classes' was received from the result of parser. 
    ClassTable *classtable = new ClassTable(classes);

    /* some semantic analysis code may go here */

    if (classtable->errors()) {
        cerr << "Compilation halted due to static semantic errors." << endl;
        exit(1);
    }
}


