<?php
    if(isset($_GET["coordinates"])) {
        // echo "./explorer " . $_GET["coordinates"];
        exec("../c/bin/explorer " . $_GET["coordinates"], $out);
        foreach ($out as $item) {
            echo $item . "\n";
        }
    }
    // $result = explode(" ", $out[0]);
    // $angles = json_encode($result);
?>