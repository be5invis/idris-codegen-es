var diff = require('virtual-dom/diff');
var patch = require('virtual-dom/patch');
var createElement = require('virtual-dom/create-element');
var h = require('virtual-dom/h');

debug = function(x){
    var console = require('console');
    console.log(x);
}


b$node = function(tag, props, childs){
    var props2 = {};
    for(var k in props){
        props2[k] = props[k];
    }
    return h(tag, props2, childs);
}

b$tree = b$node('div','');
b$rootNode = createElement(b$tree);
document.body.appendChild(b$rootNode);


b$setDisplay = function(newTree){
    var patches = diff(b$tree, newTree);
    b$rootNode = patch(b$rootNode, patches);
    b$tree = newTree;    
}

b$list2obj = function(l){
    res = {};
    for(var v in l){
        res[l[v][0]] = l[v][1];
    }
    return res;
}


//b$post_request = function(url, id, val){
// console.log([url,id,val])
// var xmlhttp=new XMLHttpRequest();
// xmlhttp.onreadystatechange=function(){
//  if (xmlhttp.readyState==4){
//      if(xmlhttp.status==200){
//          b$stepr(id, xmlhttp.responseText);
//      }
//      else{
//          b$stepw(id, xmlhttp.statusText)
//      } 
//  }
// }
// xmlhttp.open("POST",url,true);
// xmlhttp.send(val);
//}
