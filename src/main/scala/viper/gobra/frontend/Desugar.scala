package viper.gobra.frontend

import viper.gobra.ast.parser.PProgram
import viper.gobra.ast.internal.Program

object Desugar {

  def desugar(program: PProgram, info: TypeInfo): Program = {
    Program()
  }
}

