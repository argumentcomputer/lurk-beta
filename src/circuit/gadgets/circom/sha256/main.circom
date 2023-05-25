/*
    Copyright 2018 0KIMS association.

    This file is part of circom (Zero Knowledge Circuit Compiler).

    circom is a free software: you can redistribute it and/or modify it
    under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    circom is distributed in the hope that it will be useful, but WITHOUT
    ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
    or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public
    License for more details.

    You should have received a copy of the GNU General Public License
    along with circom. If not, see <https://www.gnu.org/licenses/>.
*/
pragma circom 2.0.0;

include "sha256_2.circom";

template Main() {
    signal input arg_in[2];
    signal output arg_out[1];

    component sha256_2 = Sha256_2();

    sha256_2.a <== arg_in[0];
    sha256_2.b <== arg_in[1];
    arg_out[0] <== sha256_2.out;
}
component main { public [arg_in] } = Main();
