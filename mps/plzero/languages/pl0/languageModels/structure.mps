<?xml version="1.0" encoding="UTF-8"?>
<model modelUID="r:f052d088-2c7b-4428-8b1d-dd4b1c4d192f(pl0.structure)" version="7">
  <persistence version="8" />
  <language namespace="c72da2b9-7cce-4447-8389-f407dc1158b7(jetbrains.mps.lang.structure)" />
  <devkit namespace="fbc25dd2-5da4-483a-8b19-70928e1b62d7(jetbrains.mps.devkit.general-purpose)" />
  <import index="tpce" modelUID="r:00000000-0000-4000-0000-011c89590292(jetbrains.mps.lang.structure.structure)" version="0" implicit="yes" />
  <import index="tpck" modelUID="r:00000000-0000-4000-0000-011c89590288(jetbrains.mps.lang.core.structure)" version="0" implicit="yes" />
  <import index="vydg" modelUID="r:f052d088-2c7b-4428-8b1d-dd4b1c4d192f(pl0.structure)" version="7" implicit="yes" />
  <root type="tpce.ConceptDeclaration" typeId="tpce.1071489090640" id="714196159579087055" nodeInfo="ig">
    <property name="name" nameId="tpck.1169194664001" value="IntLiteral" />
    <property name="virtualPackage" nameId="tpck.1193676396447" value="prim" />
    <link role="extends" roleId="tpce.1071489389519" targetNodeId="714196159579090577" resolveInfo="Expr" />
    <node role="propertyDeclaration" roleId="tpce.1071489727084" type="tpce.PropertyDeclaration" typeId="tpce.1071489288299" id="714196159579090571" nodeInfo="ig">
      <property name="name" nameId="tpck.1169194664001" value="value" />
      <link role="dataType" roleId="tpce.1082985295845" targetNodeId="tpck.1082983657062" resolveInfo="integer" />
    </node>
  </root>
  <root type="tpce.ConceptDeclaration" typeId="tpce.1071489090640" id="714196159579090577" nodeInfo="ig">
    <property name="name" nameId="tpck.1169194664001" value="Expr" />
    <property name="abstract" nameId="tpce.4628067390765956802" value="true" />
    <property name="final" nameId="tpce.4628067390765956807" value="false" />
    <link role="extends" roleId="tpce.1071489389519" targetNodeId="tpck.1133920641626" resolveInfo="BaseConcept" />
  </root>
  <root type="tpce.ConceptDeclaration" typeId="tpce.1071489090640" id="714196159579092483" nodeInfo="ig">
    <property name="virtualPackage" nameId="tpck.1193676396447" value="type" />
    <property name="name" nameId="tpck.1169194664001" value="TInteger" />
    <link role="extends" roleId="tpce.1071489389519" targetNodeId="tpck.1133920641626" resolveInfo="BaseConcept" />
  </root>
  <root type="tpce.ConceptDeclaration" typeId="tpce.1071489090640" id="714196159579117599" nodeInfo="ig">
    <property name="virtualPackage" nameId="tpck.1193676396447" value="type" />
    <property name="name" nameId="tpck.1169194664001" value="TValue" />
    <property name="abstract" nameId="tpce.4628067390765956802" value="true" />
    <link role="extends" roleId="tpce.1071489389519" targetNodeId="tpck.1133920641626" resolveInfo="BaseConcept" />
  </root>
  <root type="tpce.ConceptDeclaration" typeId="tpce.1071489090640" id="714196159579165182" nodeInfo="ig">
    <property name="virtualPackage" nameId="tpck.1193676396447" value="type" />
    <property name="name" nameId="tpck.1169194664001" value="TBoolean" />
    <property name="abstract" nameId="tpce.4628067390765956802" value="true" />
    <link role="extends" roleId="tpce.1071489389519" targetNodeId="714196159579117599" resolveInfo="TValue" />
  </root>
  <root type="tpce.ConceptDeclaration" typeId="tpce.1071489090640" id="714196159579168284" nodeInfo="ig">
    <property name="name" nameId="tpck.1169194664001" value="Odd" />
    <property name="conceptAlias" nameId="tpce.5092175715804935370" value="odd" />
    <link role="extends" roleId="tpce.1071489389519" targetNodeId="714196159579090577" resolveInfo="Expr" />
    <node role="linkDeclaration" roleId="tpce.1071489727083" type="tpce.LinkDeclaration" typeId="tpce.1071489288298" id="714196159579179398" nodeInfo="ig">
      <property name="metaClass" nameId="tpce.1071599937831" value="aggregation" />
      <property name="sourceCardinality" nameId="tpce.1071599893252" value="1" />
      <property name="role" nameId="tpce.1071599776563" value="y" />
      <link role="target" roleId="tpce.1071599976176" targetNodeId="714196159579090577" resolveInfo="Expr" />
    </node>
  </root>
  <root type="tpce.ConceptDeclaration" typeId="tpce.1071489090640" id="714196159579189204" nodeInfo="ig">
    <property name="name" nameId="tpck.1169194664001" value="Program" />
    <property name="rootable" nameId="tpce.1096454100552" value="true" />
    <link role="extends" roleId="tpce.1071489389519" targetNodeId="tpck.1133920641626" resolveInfo="BaseConcept" />
    <node role="linkDeclaration" roleId="tpce.1071489727083" type="tpce.LinkDeclaration" typeId="tpce.1071489288298" id="714196159579281321" nodeInfo="ig">
      <property name="metaClass" nameId="tpce.1071599937831" value="aggregation" />
      <property name="role" nameId="tpce.1071599776563" value="vars" />
      <property name="sourceCardinality" nameId="tpce.1071599893252" value="1" />
      <link role="target" roleId="tpce.1071599976176" targetNodeId="714196159579281326" resolveInfo="VarDefs" />
    </node>
    <node role="linkDeclaration" roleId="tpce.1071489727083" type="tpce.LinkDeclaration" typeId="tpce.1071489288298" id="714196159579189310" nodeInfo="ig">
      <property name="metaClass" nameId="tpce.1071599937831" value="aggregation" />
      <property name="role" nameId="tpce.1071599776563" value="block" />
      <property name="sourceCardinality" nameId="tpce.1071599893252" value="1" />
      <link role="target" roleId="tpce.1071599976176" targetNodeId="714196159579189294" resolveInfo="Block" />
    </node>
  </root>
  <root type="tpce.ConceptDeclaration" typeId="tpce.1071489090640" id="714196159579189267" nodeInfo="ig">
    <property name="name" nameId="tpck.1169194664001" value="BeginStmt" />
    <link role="extends" roleId="tpce.1071489389519" targetNodeId="714196159579189280" resolveInfo="Stmt" />
    <node role="linkDeclaration" roleId="tpce.1071489727083" type="tpce.LinkDeclaration" typeId="tpce.1071489288298" id="714196159579236014" nodeInfo="ig">
      <property name="metaClass" nameId="tpce.1071599937831" value="aggregation" />
      <property name="role" nameId="tpce.1071599776563" value="statements" />
      <property name="sourceCardinality" nameId="tpce.1071599893252" value="0..n" />
      <link role="target" roleId="tpce.1071599976176" targetNodeId="714196159579189280" resolveInfo="Stmt" />
    </node>
  </root>
  <root type="tpce.ConceptDeclaration" typeId="tpce.1071489090640" id="714196159579189280" nodeInfo="ig">
    <property name="name" nameId="tpck.1169194664001" value="Stmt" />
    <property name="abstract" nameId="tpce.4628067390765956802" value="true" />
    <property name="final" nameId="tpce.4628067390765956807" value="false" />
    <link role="extends" roleId="tpce.1071489389519" targetNodeId="tpck.1133920641626" resolveInfo="BaseConcept" />
  </root>
  <root type="tpce.ConceptDeclaration" typeId="tpce.1071489090640" id="714196159579189294" nodeInfo="ig">
    <property name="name" nameId="tpck.1169194664001" value="Block" />
    <link role="extends" roleId="tpce.1071489389519" targetNodeId="tpck.1133920641626" resolveInfo="BaseConcept" />
    <node role="linkDeclaration" roleId="tpce.1071489727083" type="tpce.LinkDeclaration" typeId="tpce.1071489288298" id="714196159579207550" nodeInfo="ig">
      <property name="metaClass" nameId="tpce.1071599937831" value="aggregation" />
      <property name="role" nameId="tpce.1071599776563" value="statement" />
      <property name="sourceCardinality" nameId="tpce.1071599893252" value="1" />
      <link role="target" roleId="tpce.1071599976176" targetNodeId="714196159579189280" resolveInfo="Stmt" />
    </node>
  </root>
  <root type="tpce.ConceptDeclaration" typeId="tpce.1071489090640" id="714196159579236061" nodeInfo="ig">
    <property name="name" nameId="tpck.1169194664001" value="AssignStmt" />
    <link role="extends" roleId="tpce.1071489389519" targetNodeId="714196159579189280" resolveInfo="Stmt" />
    <node role="linkDeclaration" roleId="tpce.1071489727083" type="tpce.LinkDeclaration" typeId="tpce.1071489288298" id="714196159579236078" nodeInfo="ig">
      <property name="metaClass" nameId="tpce.1071599937831" value="aggregation" />
      <property name="role" nameId="tpce.1071599776563" value="lhs" />
      <property name="sourceCardinality" nameId="tpce.1071599893252" value="1" />
      <link role="target" roleId="tpce.1071599976176" targetNodeId="714196159579236103" resolveInfo="VarRef" />
    </node>
    <node role="linkDeclaration" roleId="tpce.1071489727083" type="tpce.LinkDeclaration" typeId="tpce.1071489288298" id="714196159579257958" nodeInfo="ig">
      <property name="metaClass" nameId="tpce.1071599937831" value="aggregation" />
      <property name="role" nameId="tpce.1071599776563" value="rhs" />
      <property name="sourceCardinality" nameId="tpce.1071599893252" value="1" />
      <link role="target" roleId="tpce.1071599976176" targetNodeId="714196159579090577" resolveInfo="Expr" />
    </node>
  </root>
  <root type="tpce.ConceptDeclaration" typeId="tpce.1071489090640" id="714196159579236082" nodeInfo="ig">
    <property name="name" nameId="tpck.1169194664001" value="VarDef" />
    <link role="extends" roleId="tpce.1071489389519" targetNodeId="tpck.1133920641626" resolveInfo="BaseConcept" />
    <node role="propertyDeclaration" roleId="tpce.1071489727084" type="tpce.PropertyDeclaration" typeId="tpce.1071489288299" id="714196159579257822" nodeInfo="ig">
      <property name="name" nameId="tpck.1169194664001" value="iden" />
      <link role="dataType" roleId="tpce.1082985295845" targetNodeId="tpck.1082983041843" resolveInfo="string" />
    </node>
  </root>
  <root type="tpce.ConceptDeclaration" typeId="tpce.1071489090640" id="714196159579236103" nodeInfo="ig">
    <property name="name" nameId="tpck.1169194664001" value="VarRef" />
    <link role="extends" roleId="tpce.1071489389519" targetNodeId="714196159579090577" resolveInfo="Expr" />
    <node role="linkDeclaration" roleId="tpce.1071489727083" type="tpce.LinkDeclaration" typeId="tpce.1071489288298" id="714196159579236104" nodeInfo="ig">
      <property name="metaClass" nameId="tpce.1071599937831" value="reference" />
      <property name="role" nameId="tpce.1071599776563" value="var" />
      <property name="sourceCardinality" nameId="tpce.1071599893252" value="1" />
      <link role="target" roleId="tpce.1071599976176" targetNodeId="714196159579236082" resolveInfo="VarDef" />
    </node>
  </root>
  <root type="tpce.ConceptDeclaration" typeId="tpce.1071489090640" id="714196159579281326" nodeInfo="ig">
    <property name="name" nameId="tpck.1169194664001" value="VarDefs" />
    <link role="extends" roleId="tpce.1071489389519" targetNodeId="tpck.1133920641626" resolveInfo="BaseConcept" />
    <node role="linkDeclaration" roleId="tpce.1071489727083" type="tpce.LinkDeclaration" typeId="tpce.1071489288298" id="714196159579281327" nodeInfo="ig">
      <property name="metaClass" nameId="tpce.1071599937831" value="aggregation" />
      <property name="role" nameId="tpce.1071599776563" value="vars" />
      <property name="sourceCardinality" nameId="tpce.1071599893252" value="0..n" />
      <link role="target" roleId="tpce.1071599976176" targetNodeId="714196159579236082" resolveInfo="VarDef" />
    </node>
  </root>
  <root type="tpce.ConceptDeclaration" typeId="tpce.1071489090640" id="714196159579434503" nodeInfo="ig">
    <property name="name" nameId="tpck.1169194664001" value="DyadicExpr" />
    <link role="extends" roleId="tpce.1071489389519" targetNodeId="714196159579090577" resolveInfo="Expr" />
    <node role="linkDeclaration" roleId="tpce.1071489727083" type="tpce.LinkDeclaration" typeId="tpce.1071489288298" id="714196159579434504" nodeInfo="ig">
      <property name="metaClass" nameId="tpce.1071599937831" value="aggregation" />
      <property name="role" nameId="tpce.1071599776563" value="x" />
      <property name="sourceCardinality" nameId="tpce.1071599893252" value="1" />
      <link role="target" roleId="tpce.1071599976176" targetNodeId="714196159579090577" resolveInfo="Expr" />
    </node>
    <node role="linkDeclaration" roleId="tpce.1071489727083" type="tpce.LinkDeclaration" typeId="tpce.1071489288298" id="714196159579435095" nodeInfo="ig">
      <property name="metaClass" nameId="tpce.1071599937831" value="aggregation" />
      <property name="role" nameId="tpce.1071599776563" value="verb" />
      <property name="sourceCardinality" nameId="tpce.1071599893252" value="1" />
      <link role="target" roleId="tpce.1071599976176" targetNodeId="714196159579491715" resolveInfo="Verb" />
    </node>
    <node role="linkDeclaration" roleId="tpce.1071489727083" type="tpce.LinkDeclaration" typeId="tpce.1071489288298" id="714196159579434509" nodeInfo="ig">
      <property name="metaClass" nameId="tpce.1071599937831" value="aggregation" />
      <property name="role" nameId="tpce.1071599776563" value="y" />
      <property name="sourceCardinality" nameId="tpce.1071599893252" value="1" />
      <link role="target" roleId="tpce.1071599976176" targetNodeId="714196159579090577" resolveInfo="Expr" />
    </node>
  </root>
  <root type="tpce.EnumerationDataTypeDeclaration" typeId="tpce.1082978164219" id="714196159579483589" nodeInfo="ng">
    <property name="name" nameId="tpck.1169194664001" value="VerbEnum" />
    <property name="memberIdentifierPolicy" nameId="tpce.1197591154882" value="derive_from_internal_value" />
    <link role="memberDataType" roleId="tpce.1083171729157" targetNodeId="tpck.1082983041843" resolveInfo="string" />
    <node role="member" roleId="tpce.1083172003582" type="tpce.EnumerationMemberDeclaration" typeId="tpce.1083171877298" id="714196159579483590" nodeInfo="ig">
      <property name="externalValue" nameId="tpce.1083923523172" value="+" />
      <property name="internalValue" nameId="tpce.1083923523171" value="add" />
    </node>
    <node role="member" roleId="tpce.1083172003582" type="tpce.EnumerationMemberDeclaration" typeId="tpce.1083171877298" id="714196159579483622" nodeInfo="ig">
      <property name="externalValue" nameId="tpce.1083923523172" value="-" />
      <property name="internalValue" nameId="tpce.1083923523171" value="sub" />
    </node>
    <node role="member" roleId="tpce.1083172003582" type="tpce.EnumerationMemberDeclaration" typeId="tpce.1083171877298" id="714196159579483625" nodeInfo="ig">
      <property name="externalValue" nameId="tpce.1083923523172" value="*" />
      <property name="internalValue" nameId="tpce.1083923523171" value="mul" />
    </node>
    <node role="member" roleId="tpce.1083172003582" type="tpce.EnumerationMemberDeclaration" typeId="tpce.1083171877298" id="714196159579483629" nodeInfo="ig">
      <property name="externalValue" nameId="tpce.1083923523172" value="/" />
      <property name="internalValue" nameId="tpce.1083923523171" value="div" />
    </node>
  </root>
  <root type="tpce.ConceptDeclaration" typeId="tpce.1071489090640" id="714196159579491715" nodeInfo="ig">
    <property name="name" nameId="tpck.1169194664001" value="Verb" />
    <link role="extends" roleId="tpce.1071489389519" targetNodeId="tpck.1133920641626" resolveInfo="BaseConcept" />
    <node role="propertyDeclaration" roleId="tpce.1071489727084" type="tpce.PropertyDeclaration" typeId="tpce.1071489288299" id="714196159579491788" nodeInfo="ig">
      <property name="name" nameId="tpck.1169194664001" value="symbol" />
      <link role="dataType" roleId="tpce.1082985295845" targetNodeId="714196159579483589" resolveInfo="VerbEnum" />
    </node>
  </root>
</model>

