/*
* @name Unsafe XML Deserialization
* @kind path-problem
* @id java/unsafe-deserialization
*/
import java
import semmle.code.java.dataflow.DataFlow
import DataFlow::PathGraph

// All mehtod calls
// from MethodAccess m
// select m 


//Method being called by each method call
//mine
// from Method m
// select m.getACallee()

//Actual
// from Method method, MethodAccess call
// where call.getMethod() = method 
// select call, method


// call in program to method fromXML
//mine
// from MethodAccess call, Method m
// where call.getMethod() = m and m.hasName("fromXML")
// select call, m


//Actual
// from MethodAccess call, Method m
// where call.getMethod() = m and m.getName() = "fromXML"
// select call, m

// from MethodAccess call
// where call.getMethod().getName() = "fromXML"
// select call


//Xstream.fromXML desearlizes first Argument. query deserialized arguments
// from MethodAccess call, Expr arg
// where call.getMethod().getName() = "fromXML" and arg = call.getArgument(0)
// select call, arg



//conver your query into a predicate

predicate isXMLDeserialized(Expr arg) {
    exists(MethodAccess fromXML | 
            fromXML.getMethod().hasName("fromXML") and arg = fromXML.getArgument(0)
        )
    
}

// from Expr arg
// where isXMLDeserialized(arg)
// select arg




// Step 2



// write to codeQL class to find ContentTypeHandler interface

class ContentTypeHandler extends RefType{
    ContentTypeHandler(){
        this.hasQualifiedName("org.apache.struts2.rest.handler", "ContentTypeHandler")
    }
}



// Create a CodeQL class called ContentTypeHandlerToObject for identfying Methods called toObject on classes whose direct super-types include ContentTypeHandler.


class ContentTypeHandlerToObject extends Method {
    ContentTypeHandlerToObject(){
        this.getDeclaringType().getASupertype() instanceof ContentTypeHandler and
        this.hasName("toObject")
    }
}

// from ContentTypeHandlerToObject ctho
// select ctho.getParameter(0)









// step 3: Dataflow analysis

class StrutsUnsafeDeserializationConfig extends DataFlow::Configuration{
    StrutsUnsafeDeserializationConfig(){
        this = "StrutsUnsafeDeserializationConfig"
    }

    override predicate isSource(DataFlow::Node source){
        exists(ContentTypeHandlerToObject toObjectMethod   |
        source.asParameter() = toObjectMethod.getParameter(0)
        )
    }

    
    override predicate isSink(DataFlow::Node sink){
        exists(Expr arg | 
            isXMLDeserialized(arg) and
            sink.asExpr() = arg
            )
    }
}

from StrutsUnsafeDeserializationConfig config, DataFlow::PathNode source, DataFlow::PathNode sink
where config.hasFlowPath(source, sink)
select sink,source, sink, "Unsafe XML Deserialization"