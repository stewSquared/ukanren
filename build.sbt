scalaVersion := "2.11.7"

libraryDependencies += "com.lihaoyi" %% "utest" % "0.3.1"

testFrameworks += new TestFramework("utest.runner.Framework")
