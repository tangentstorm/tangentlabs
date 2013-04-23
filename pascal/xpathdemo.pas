program xpathdemo;
uses xpath, xmlread, DOM;
{  from xpath:
  function EvaluateXPathExpression(
             const AExpressionString : dom.DOMString;
             AContextNode      : dom.TDOMNode;
	     AResolver	       : TXPathNSResolver = nil): TXPathVariable;
}

var
  doc  : DOM.TXMLDocument;
  item : pointer;
begin
  xmlread.ReadXMLFile( doc, 'xpathdemo.xml' );
  writeln('title: ', EvaluateXPathExpression( '//title', doc ).AsText);
  for item in EvaluateXPathExpression( '//li', doc ).AsNodeSet do begin
    writeln( TDOMNode( item ).textContent );
  end;
end.

{ output
  ------
  title: xpath demo
  item one
  item two
  item three
}
