// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2020 ETH Zurich.

package viper.gobra.frontend.info.implementation.typing.ghost

import org.bitbucket.inkytonik.kiama.util.Messaging.{Messages, message}
import viper.gobra.ast.frontend._
import viper.gobra.frontend.info.base.Type._
import viper.gobra.frontend.info.implementation.TypeInfoImpl
import viper.gobra.frontend.info.implementation.typing.BaseTyping

trait GhostTypeTyping extends BaseTyping { this : TypeInfoImpl =>

  private[typing] def wellDefGhostType(typ : PGhostType) : Messages = typ match {
    case PSequenceType(elem) => isType(elem).out ++
      message(typ, s"sequences of custom defined types are currently not supported", elem.isInstanceOf[PNamedOperand])
    case PSetType(elem) => isType(elem).out ++
      message(typ, s"sets of custom defined types are currently not supported", elem.isInstanceOf[PNamedOperand])
    case PMultisetType(elem) => isType(elem).out ++
      message(typ, s"multisets of custom defined types are currently not supported", elem.isInstanceOf[PNamedOperand])
  }

  private[typing] def ghostTypeType(typ : PGhostType) : Type = typ match {
    case PSequenceType(elem) => SequenceT(typeType(elem))
    case PSetType(elem) => SetT(typeType(elem))
    case PMultisetType(elem) => MultisetT(typeType(elem))
  }
}
