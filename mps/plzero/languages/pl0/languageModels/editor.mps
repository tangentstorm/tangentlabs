<?xml version="1.0" encoding="UTF-8"?>
<model modelUID="r:380caaf7-4b5a-4ca9-974a-dfee9bb789a9(pl0.editor)">
  <persistence version="8" />
  <language namespace="18bc6592-03a6-4e29-a83a-7ff23bde13ba(jetbrains.mps.lang.editor)" />
  <devkit namespace="fbc25dd2-5da4-483a-8b19-70928e1b62d7(jetbrains.mps.devkit.general-purpose)" />
  <import index="vydg" modelUID="r:f052d088-2c7b-4428-8b1d-dd4b1c4d192f(pl0.structure)" version="4" />
  <import index="tpc2" modelUID="r:00000000-0000-4000-0000-011c8959029e(jetbrains.mps.lang.editor.structure)" version="32" implicit="yes" />
  <import index="tpck" modelUID="r:00000000-0000-4000-0000-011c89590288(jetbrains.mps.lang.core.structure)" version="0" implicit="yes" />
  <root type="tpc2.ConceptEditorDeclaration" typeId="tpc2.1071666914219" id="714196159579090607" nodeInfo="ng">
    <property name="virtualPackage" nameId="tpck.1193676396447" value="prim" />
    <link role="conceptDeclaration" roleId="tpc2.1166049300910" targetNodeId="vydg.714196159579087055" resolveInfo="IntLiteral" />
    <node role="cellModel" roleId="tpc2.1080736633877" type="tpc2.CellModel_Property" typeId="tpc2.1073389658414" id="714196159579090660" nodeInfo="ng">
      <link role="relationDeclaration" roleId="tpc2.1140103550593" targetNodeId="vydg.714196159579090571" resolveInfo="value" />
    </node>
  </root>
  <root type="tpc2.ConceptEditorDeclaration" typeId="tpc2.1071666914219" id="714196159579103677" nodeInfo="ng">
    <property name="virtualPackage" nameId="tpck.1193676396447" value="type" />
    <link role="conceptDeclaration" roleId="tpc2.1166049300910" targetNodeId="vydg.714196159579092483" resolveInfo="TInteger" />
    <node role="cellModel" roleId="tpc2.1080736633877" type="tpc2.CellModel_Constant" typeId="tpc2.1073389577006" id="714196159579103730" nodeInfo="nn">
      <property name="text" nameId="tpc2.1073389577007" value="INTEGER" />
    </node>
  </root>
  <root type="tpc2.ConceptEditorDeclaration" typeId="tpc2.1071666914219" id="714196159579179500" nodeInfo="ng">
    <link role="conceptDeclaration" roleId="tpc2.1166049300910" targetNodeId="vydg.714196159579168284" resolveInfo="Odd" />
    <node role="cellModel" roleId="tpc2.1080736633877" type="tpc2.CellModel_Collection" typeId="tpc2.1073389446423" id="714196159579179559" nodeInfo="nn">
      <node role="childCellModel" roleId="tpc2.1073389446424" type="tpc2.CellModel_Constant" typeId="tpc2.1073389577006" id="714196159579179561" nodeInfo="nn">
        <property name="text" nameId="tpc2.1073389577007" value="odd" />
      </node>
      <node role="childCellModel" roleId="tpc2.1073389446424" type="tpc2.CellModel_RefNode" typeId="tpc2.1073389882823" id="714196159579179569" nodeInfo="ng">
        <link role="relationDeclaration" roleId="tpc2.1140103550593" targetNodeId="vydg.714196159579179398" />
      </node>
      <node role="cellLayout" roleId="tpc2.1106270802874" type="tpc2.CellLayout_Indent" typeId="tpc2.1237303669825" id="714196159579179562" nodeInfo="nn" />
    </node>
  </root>
  <root type="tpc2.ConceptEditorDeclaration" typeId="tpc2.1071666914219" id="714196159579189350" nodeInfo="ng">
    <link role="conceptDeclaration" roleId="tpc2.1166049300910" targetNodeId="vydg.714196159579189204" resolveInfo="Program" />
    <node role="cellModel" roleId="tpc2.1080736633877" type="tpc2.CellModel_Collection" typeId="tpc2.1073389446423" id="714196159579189352" nodeInfo="nn">
      <node role="childCellModel" roleId="tpc2.1073389446424" type="tpc2.CellModel_RefNode" typeId="tpc2.1073389882823" id="714196159579189359" nodeInfo="ng">
        <link role="relationDeclaration" roleId="tpc2.1140103550593" targetNodeId="vydg.714196159579189310" />
      </node>
      <node role="childCellModel" roleId="tpc2.1073389446424" type="tpc2.CellModel_Constant" typeId="tpc2.1073389577006" id="714196159579189364" nodeInfo="nn">
        <property name="text" nameId="tpc2.1073389577007" value="." />
        <node role="styleItem" roleId="tpc2.1219418656006" type="tpc2.PunctuationLeftStyleClassItem" typeId="tpc2.1233758997495" id="714196159579189514" nodeInfo="nn">
          <property name="flag" nameId="tpc2.1186414551515" value="true" />
        </node>
      </node>
      <node role="cellLayout" roleId="tpc2.1106270802874" type="tpc2.CellLayout_Indent" typeId="tpc2.1237303669825" id="714196159579189355" nodeInfo="nn" />
    </node>
  </root>
  <root type="tpc2.ConceptEditorDeclaration" typeId="tpc2.1071666914219" id="714196159579189583" nodeInfo="ng">
    <link role="conceptDeclaration" roleId="tpc2.1166049300910" targetNodeId="vydg.714196159579189267" resolveInfo="BeginStmt" />
    <node role="cellModel" roleId="tpc2.1080736633877" type="tpc2.CellModel_Collection" typeId="tpc2.1073389446423" id="714196159579189585" nodeInfo="nn">
      <node role="childCellModel" roleId="tpc2.1073389446424" type="tpc2.CellModel_Constant" typeId="tpc2.1073389577006" id="714196159579189592" nodeInfo="nn">
        <property name="text" nameId="tpc2.1073389577007" value="begin" />
      </node>
      <node role="childCellModel" roleId="tpc2.1073389446424" type="tpc2.CellModel_Constant" typeId="tpc2.1073389577006" id="714196159579189598" nodeInfo="nn">
        <property name="text" nameId="tpc2.1073389577007" value="end" />
      </node>
      <node role="cellLayout" roleId="tpc2.1106270802874" type="tpc2.CellLayout_Indent" typeId="tpc2.1237303669825" id="714196159579189588" nodeInfo="nn" />
    </node>
  </root>
  <root type="tpc2.ConceptEditorDeclaration" typeId="tpc2.1071666914219" id="714196159579207546" nodeInfo="ng">
    <link role="conceptDeclaration" roleId="tpc2.1166049300910" targetNodeId="vydg.714196159579189294" resolveInfo="Block" />
    <node role="cellModel" roleId="tpc2.1080736633877" type="tpc2.CellModel_RefNode" typeId="tpc2.1073389882823" id="714196159579210414" nodeInfo="ng">
      <link role="relationDeclaration" roleId="tpc2.1140103550593" targetNodeId="vydg.714196159579207550" />
    </node>
  </root>
</model>

