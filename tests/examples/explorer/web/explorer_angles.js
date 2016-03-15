var orientation = 0;
var coordinates = {x:100, y:50};

$(document).ready(function() {
    // moveOnGrid(-1, -1);
    // moveOnGrid(1,2);
    // moveOnGrid(-1,2);
    // moveOnGrid(-1,2);
    // moveOnGrid(-1,1);
    // moveOnGrid(-1,0);
    // moveOnGrid(0,-2);
    // moveOnGrid(1,-2);
    // moveOnGrid(2,0);
    // moveOnGrid(-1,0);
    // moveOnGrid(-1,-5);
});

function initExplorer(or) {
    $("#img").rotate(or);
    orientation = or;
    $("#angle").text(orientation);
}

function moveOnGrid(y_change, x_change) {
    var x = 100 * x_change;
    var y = 100 * y_change;
    var left_direction = "+=" + x;
    var top_direction = "+=" + y;
    if(x == 0 && y > 0) {
        angle = 90;
    } else if(x == 0 && y < 0) {
        angle = -90;
    } else if(x > 0) {
        angle = Math.atan(y/x) * 180 / Math.PI;
    } else if(x < 0) {
        angle = 180 + Math.atan(y/x) * 180 / Math.PI;;
    }
    $("#angle").text(angle);
    $("img").rotate({
        duration: 1000,
        angle: orientation, 
        animateTo: angle,
        easing: $.easing.easeInOutElastic
    });
    window.setTimeout(function(){moveExplorer(left_direction, top_direction);}, 1000);
    // orientation += angle;
}


function moveOnAngle(turn) {
    var turn_time = Math.abs(turn) * 30;
    var radians = (orientation + turn) * Math.PI / 180;
    var y = Math.sin(radians) * 100;
    var x = Math.cos(radians) * 100;
    var left_direction = "+=" + x;
    var top_direction = "+=" + y;
    $("img").rotate({
        duration: turn_time,
        angle: orientation, 
        animateTo: orientation + turn,
        easing: $.easing.easeInOutElastic
    });
    window.setTimeout(function(){moveExplorer(left_direction, top_direction);}, turn_time * 1/2);
    orientation += turn;
}

function moveExplorer(left_direction, top_direction) {
    $("img").animate({left: left_direction, top: top_direction}, 2000);
}

function moveOnRoute() {
    var input = getAngles();
    var turns = calculateTurns(input);
    var move_times = calculateMoveTimes(turns);
    $("#angle").text(turns);  
    for (i = 0; i < turns.length; i++) { 
        (function(index) {
            setTimeout(function() { moveOnAngle(turns[index]); }, move_times[index]);
        })(i);
    }
}

function getAngles() {
    var xmlHttp = new XMLHttpRequest();
    xmlHttp.open( "GET", "control.php", false );
    xmlHttp.send( null );
    return JSON.parse(xmlHttp.responseText);
}

function calculateTurns(arr) { 
    var turns = [];
    for(i = 0; i < arr.length; i++) {
        var turn = parseInt(arr[i]) % 360;
        if(turn > 180) {
            turn = -360 + turn;
        }
        turns.push(turn);
    }
    return turns;
}

function calculateMoveTimes(turns) {
    var move_times = [0]; 
    for (i = 0; i < turns.length - 1; i++) { 
        running_total = move_times[i];
        move_times.push(running_total + Math.abs(turns[i]) * 30 + 2000);
    }  
    return move_times; 
}


