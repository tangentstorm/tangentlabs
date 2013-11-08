<?xml version="1.0" encoding="UTF-8"?>
<model modelUID="r:380caaf7-4b5a-4ca9-974a-dfee9bb789a9(pl0.editor)">
  <persistence version="8" />
  <language namespace="18bc6592-03a6-4e29-a83a-7ff23bde13ba(jetbrains.mps.lang.editor)" />
  <devkit namespace="fbc25dd2-5da4-483a-8b19-70928e1b62d7(jetbrains.mps.devkit.general-purpose)" />
  <import index="tpc2" modelUID="r:00000000-0000-4000-0000-011c8959029e(jetbrains.mps.lang.editor.structure)" version="32" implicit="yes" />
  <import index="vydg" modelUID="r:f052d088-2c7b-4428-8b1d-dd4b1c4d192f(pl0.structure)" version="1" implicit="yes" />
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
</model>

