<?xml version="1.0" encoding="UTF-8"?>
<model modelUID="r:2941aef1-0647-4d73-9788-04507fba3d91(pl0.sandbox)">
  <persistence version="8" />
  <language namespace="263837a3-9a9e-4073-9f5e-6e30b422555d(pl0)" />
  <language namespace="ceab5195-25ea-4f22-9b92-103b95ca8c0c(jetbrains.mps.lang.core)" />
  <import index="vydg" modelUID="r:f052d088-2c7b-4428-8b1d-dd4b1c4d192f(pl0.structure)" version="7" implicit="yes" />
  <root type="vydg.Program" typeId="vydg.714196159579189204" id="714196159579321104" nodeInfo="ng">
    <node role="vars" roleId="vydg.714196159579281321" type="vydg.VarDefs" typeId="vydg.714196159579281326" id="714196159579321105" nodeInfo="ng">
      <node role="vars" roleId="vydg.714196159579281327" type="vydg.VarDef" typeId="vydg.714196159579236082" id="714196159579355864" nodeInfo="ng">
        <property name="iden" nameId="vydg.714196159579257822" value="x" />
      </node>
      <node role="vars" roleId="vydg.714196159579281327" type="vydg.VarDef" typeId="vydg.714196159579236082" id="714196159579427043" nodeInfo="ng">
        <property name="iden" nameId="vydg.714196159579257822" value="y" />
      </node>
    </node>
    <node role="block" roleId="vydg.714196159579189310" type="vydg.Block" typeId="vydg.714196159579189294" id="714196159579321106" nodeInfo="ng">
      <node role="statement" roleId="vydg.714196159579207550" type="vydg.BeginStmt" typeId="vydg.714196159579189267" id="714196159579321110" nodeInfo="ng">
        <node role="statements" roleId="vydg.714196159579236014" type="vydg.AssignStmt" typeId="vydg.714196159579236061" id="714196159579434430" nodeInfo="ng">
          <node role="rhs" roleId="vydg.714196159579257958" type="vydg.IntLiteral" typeId="vydg.714196159579087055" id="714196159579434446" nodeInfo="ng">
            <property name="value" nameId="vydg.714196159579090571" value="1" />
          </node>
          <node role="lhs" roleId="vydg.714196159579236078" type="vydg.VarRef" typeId="vydg.714196159579236103" id="714196159579434444" nodeInfo="ng">
            <link role="var" roleId="vydg.714196159579236104" targetNodeId="714196159579427043" />
          </node>
        </node>
        <node role="statements" roleId="vydg.714196159579236014" type="vydg.AssignStmt" typeId="vydg.714196159579236061" id="714196159579321117" nodeInfo="ng">
          <node role="lhs" roleId="vydg.714196159579236078" type="vydg.VarRef" typeId="vydg.714196159579236103" id="714196159579355866" nodeInfo="ng">
            <link role="var" roleId="vydg.714196159579236104" targetNodeId="714196159579355864" />
          </node>
          <node role="rhs" roleId="vydg.714196159579257958" type="vydg.DyadicExpr" typeId="vydg.714196159579434503" id="714196159579599645" nodeInfo="ng">
            <node role="x" roleId="vydg.714196159579434504" type="vydg.IntLiteral" typeId="vydg.714196159579087055" id="714196159579599761" nodeInfo="ng">
              <property name="value" nameId="vydg.714196159579090571" value="1" />
            </node>
            <node role="verb" roleId="vydg.714196159579435095" type="vydg.Verb" typeId="vydg.714196159579491715" id="714196159579599799" nodeInfo="ng">
              <property name="symbol" nameId="vydg.714196159579491788" value="sub" />
            </node>
            <node role="y" roleId="vydg.714196159579434509" type="vydg.VarRef" typeId="vydg.714196159579236103" id="714196159579599749" nodeInfo="ng">
              <link role="var" roleId="vydg.714196159579236104" targetNodeId="714196159579427043" />
            </node>
          </node>
        </node>
      </node>
    </node>
  </root>
</model>

