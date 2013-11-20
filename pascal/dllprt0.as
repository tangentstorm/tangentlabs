diff --git a/rtl/freebsd/x86_64/dllprt0.as b/rtl/freebsd/x86_64/dllprt0.as
index 7213eae..2a68c6f 100644
--- a/rtl/freebsd/x86_64/dllprt0.as
+++ b/rtl/freebsd/x86_64/dllprt0.as
@@ -68,8 +68,20 @@ _haltproc:
         movzwl  (%rbx),%edi
         syscall
         jmp     _haltproc@PLT
-	/* Do not fail linkage if argc, argv and envp are not found. */
-	.weak   operatingsystem_parameter_argc
-	.weak   operatingsystem_parameter_argv
-	.weak   operatingsystem_parameter_envp
+//	/* Do not fail linkage if argc, argv and envp are not found. */
+//	.weak   operatingsystem_parameter_argc
+//	.weak   operatingsystem_parameter_argv
+//	.weak   operatingsystem_parameter_envp
 
+/* Although these variables are useless, they actually do need to be declared
+ * to create shared libraries usable from other environments. (eg, python).
+ */
+operatingsystem_parameters:
+        .skip 3*8
+
+        .global operatingsystem_parameter_envp
+        .global operatingsystem_parameter_argc
+        .global operatingsystem_parameter_argv
+        .set operatingsystem_parameter_envp,operatingsystem_parameters+0
+        .set operatingsystem_parameter_argc,operatingsystem_parameters+8
+        .set operatingsystem_parameter_argv,operatingsystem_parameters+16
