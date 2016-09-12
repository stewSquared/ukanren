scalaVersion := "2.11.8"

organization := "com.stewsquared"

name := "ukanren"

version := "0.1-SNAPSHOT"

libraryDependencies += "com.lihaoyi" %% "utest" % "0.3.1"

testFrameworks += new TestFramework("utest.runner.Framework")
