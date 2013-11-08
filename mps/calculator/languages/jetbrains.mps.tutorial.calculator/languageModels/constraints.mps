<?xml version="1.0" encoding="UTF-8"?>
<model modelUID="r:8139d233-63b5-4a56-b7fd-77aa613acf90(jetbrains.mps.tutorial.calculator.constraints)">
  <persistence version="8" />
  <language namespace="3f4bc5f5-c6c1-4a28-8b10-c83066ffa4a1(jetbrains.mps.lang.constraints)" />
  <devkit namespace="fbc25dd2-5da4-483a-8b19-70928e1b62d7(jetbrains.mps.devkit.general-purpose)" />
  <import index="tp1t" modelUID="r:00000000-0000-4000-0000-011c8959030d(jetbrains.mps.lang.constraints.structure)" version="9" implicit="yes" />
  <import index="bbqh" modelUID="r:525d7fdc-24b4-44b3-ae44-c723d189b765(jetbrains.mps.tutorial.calculator.structure)" version="-1" implicit="yes" />
  <root type="tp1t.ConceptConstraints" typeId="tp1t.1213093968558" id="714196159577437448" nodeInfo="ng">
    <link role="concept" roleId="tp1t.1213093996982" targetNodeId="bbqh.714196159574985953" resolveInfo="InputFieldReference" />
    <node role="referent" roleId="tp1t.1213100494875" type="tp1t.NodeReferentConstraint" typeId="tp1t.1148687176410" id="714196159578536559" nodeInfo="ng">
      <link role="applicableLink" roleId="tp1t.1148687202698" targetNodeId="bbqh.714196159574987131" />
      <node role="searchScopeFactory" roleId="tp1t.1148687345559" type="tp1t.InheritedNodeScopeFactory" typeId="tp1t.8401916545537438642" id="714196159578536562" nodeInfo="ng">
        <link role="kind" roleId="tp1t.8401916545537438643" targetNodeId="bbqh.714196159574328627" resolveInfo="InputField" />
      </node>
    </node>
  </root>
</model>

