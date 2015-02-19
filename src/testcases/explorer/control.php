<?php
    exec("./test Sir", $out);
    $result = explode(" ", $out[0]);
    $angles = json_encode($result);
    echo $angles;
?>