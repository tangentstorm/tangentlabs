program domtest(output);
uses dom, xmlwrite;
  var doc : txmldocument;
begin
  doc := dom.txmldocument.create;
  writeXMLFile(doc, output);
  doc.free
end.
