<?xml version="1.0" encoding="UTF-8"?>
<model modelUID="r:6713e12f-2d7f-460b-8038-d4a52f34cd97(jetbrains.mps.tutorial.calculator.sandbox)">
  <persistence version="8" />
  <language namespace="0fe77ec8-8b4d-43d7-8080-9b7a88ee6044(jetbrains.mps.tutorial.calculator)" />
  <language namespace="f3061a53-9226-4cc5-a443-f952ceaf5816(jetbrains.mps.baseLanguage)" />
  <import index="tpck" modelUID="r:00000000-0000-4000-0000-011c89590288(jetbrains.mps.lang.core.structure)" version="0" implicit="yes" />
  <import index="bbqh" modelUID="r:525d7fdc-24b4-44b3-ae44-c723d189b765(jetbrains.mps.tutorial.calculator.structure)" version="-1" implicit="yes" />
  <import index="tpee" modelUID="r:00000000-0000-4000-0000-011c895902ca(jetbrains.mps.baseLanguage.structure)" version="4" implicit="yes" />
  <root type="bbqh.Calculator" typeId="bbqh.714196159574323305" id="714196159574328624" nodeInfo="ng">
    <property name="name" nameId="tpck.1169194664001" value="MyCalc" />
    <node role="outputField" roleId="bbqh.714196159574340734" type="bbqh.OutputField" typeId="bbqh.714196159574340672" id="714196159574373407" nodeInfo="ng">
      <node role="expression" roleId="bbqh.714196159574370022" type="tpee.PlusExpression" typeId="tpee.1068581242875" id="714196159574390724" nodeInfo="nn">
        <node role="leftExpression" roleId="tpee.1081773367580" type="tpee.IntegerConstant" typeId="tpee.1068580320020" id="714196159574389971" nodeInfo="nn">
          <property name="value" nameId="tpee.1068580320021" value="2" />
        </node>
        <node role="rightExpression" roleId="tpee.1081773367579" type="tpee.IntegerConstant" typeId="tpee.1068580320020" id="714196159574390755" nodeInfo="nn">
          <property name="value" nameId="tpee.1068580320021" value="2" />
        </node>
      </node>
    </node>
    <node role="inputField" roleId="bbqh.714196159574328734" type="bbqh.InputField" typeId="bbqh.714196159574328627" id="714196159574340636" nodeInfo="ng">
      <property name="name" nameId="tpck.1169194664001" value="width" />
    </node>
    <node role="inputField" roleId="bbqh.714196159574328734" type="bbqh.InputField" typeId="bbqh.714196159574328627" id="714196159574340639" nodeInfo="ng">
      <property name="name" nameId="tpck.1169194664001" value="height" />
    </node>
    <node role="inputField" roleId="bbqh.714196159574328734" type="bbqh.InputField" typeId="bbqh.714196159574328627" id="714196159574340644" nodeInfo="ng">
      <property name="name" nameId="tpck.1169194664001" value="depth" />
    </node>
  </root>
  <root type="bbqh.Calculator" typeId="bbqh.714196159574323305" id="714196159577395198" nodeInfo="ng">
    <property name="name" nameId="tpck.1169194664001" value="MySalary" />
    <node role="inputField" roleId="bbqh.714196159574328734" type="bbqh.InputField" typeId="bbqh.714196159574328627" id="714196159577395226" nodeInfo="ng">
      <property name="name" nameId="tpck.1169194664001" value="Java Hours" />
    </node>
    <node role="inputField" roleId="bbqh.714196159574328734" type="bbqh.InputField" typeId="bbqh.714196159574328627" id="714196159577395229" nodeInfo="ng">
      <property name="name" nameId="tpck.1169194664001" value="PHP Hours" />
    </node>
    <node role="outputField" roleId="bbqh.714196159574340734" type="bbqh.OutputField" typeId="bbqh.714196159574340672" id="714196159577395234" nodeInfo="ng">
      <node role="expression" roleId="bbqh.714196159574370022" type="tpee.PlusExpression" typeId="tpee.1068581242875" id="714196159578579189" nodeInfo="nn">
        <node role="rightExpression" roleId="tpee.1081773367579" type="tpee.MulExpression" typeId="tpee.1092119917967" id="714196159578579317" nodeInfo="nn">
          <node role="rightExpression" roleId="tpee.1081773367579" type="tpee.IntegerConstant" typeId="tpee.1068580320020" id="714196159578579320" nodeInfo="nn">
            <property name="value" nameId="tpee.1068580320021" value="10" />
          </node>
          <node role="leftExpression" roleId="tpee.1081773367580" type="bbqh.InputFieldReference" typeId="bbqh.714196159574985953" id="714196159578579308" nodeInfo="ng">
            <link role="field" roleId="bbqh.714196159574987131" targetNodeId="714196159577395229" resolveInfo="PHP Hours" />
          </node>
        </node>
        <node role="leftExpression" roleId="tpee.1081773367580" type="tpee.MulExpression" typeId="tpee.1092119917967" id="714196159578579280" nodeInfo="nn">
          <node role="rightExpression" roleId="tpee.1081773367579" type="tpee.IntegerConstant" typeId="tpee.1068580320020" id="714196159578579283" nodeInfo="nn">
            <property name="value" nameId="tpee.1068580320021" value="5" />
          </node>
          <node role="leftExpression" roleId="tpee.1081773367580" type="bbqh.InputFieldReference" typeId="bbqh.714196159574985953" id="714196159578579180" nodeInfo="ng">
            <link role="field" roleId="bbqh.714196159574987131" targetNodeId="714196159577395226" resolveInfo="Java Hours" />
          </node>
        </node>
      </node>
    </node>
  </root>
</model>

