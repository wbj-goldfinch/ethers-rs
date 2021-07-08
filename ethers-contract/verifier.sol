pragma solidity ^0.7.6;
pragma abicoder v2;

contract TestVerifier {
    struct G2Point {
        uint256[2] X;
        uint256[2] Y;
    }

    function myVerify(
        G2Point memory,
        uint256[] memory
    ) public pure returns (bool) {
        return true;
    }

}
